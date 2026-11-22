--[[
  Mage Portal Blacklist 3.0   (WoW: Forever 1.60.x, Interface 16001, modern Mainline API, Lua 5.1)

  - Works ONLY for Mages level 20+.
  - ONE blacklist shared between all mages (character names are unique per region on Forever).
  - Transport 1: addon messages in ONE private hidden channel (+ automatic chat-message fallback).
    The game keeps backend realms apart, so the channel only reaches mages on your backend realm.
  - Transport 2: direct addon whispers ("links") that also work ACROSS backend realms.
    Links are created with /mbl link Name Surname, automatically through guild addon messages,
    or automatically when a linked mage contacts you. Entries are relayed between channel and links.
  - Send results are checked; throttled messages are retried instead of being lost.
  - Only the mage who added a player can remove that player.
  - Warns (or auto-ignores) blacklisted players who whisper you / invite you to a party.
  - Minimap button, tabbed window, live sync status, /mbl debug.
]]

local ADDON        = "MageBlacklist"
local VERSION      = "3.2"
local PREFIX       = "MBL2"            -- protocol prefix (unchanged -> compatible with 2.x)
local CHANNEL_BASE = "MageBLSync"
local CHANNEL      = CHANNEL_BASE      -- ONE channel name for every mage (the game keeps backend realms apart itself)
local CHAT_TAG     = "MBL2:"           -- tag of the fallback chat transport
local MIN_LEVEL    = 20
local FS, RS       = "~", "^"          -- field / record separators
local ROWS         = 8
local HEARTBEAT    = 120               -- seconds between consistency checks (+ random jitter)
local PEER_TTL     = 330               -- a mage counts as "online" if heard within this many seconds
local PRUNE_AGE    = 60 * 60 * 24 * 30 -- removed records are purged after 30 days
local MESH_MAX     = 40                -- max number of direct links
local LINK_TTL     = 60 * 60 * 24 * 14 -- automatic links not heard for 14 days are dropped
local ICON         = "Interface\\Icons\\Spell_Arcane_PortalOrgrimmar"
local WHITE        = "Interface\\Buttons\\WHITE8X8"

local OLD_DEFAULT_1 = "Hi, you're on the mages' blacklist (unpaid portal), so I won't create a portal for you."
-- Variables: {player} = the blacklisted player, {owner} = full name of the mage who added them, {reason} = note
local DEFAULT_REPLY = "Hi {player}, you're on the mages' blacklist for an unpaid portal. Please whisper {owner}, who added you, and settle the debt - once it's paid they can remove you from the list."

local DB, S                       -- DB = entries of this realm+faction, S = settings
local me, myShort = "", ""
local enabled, warnedDisabled = false, false
local hidden = false
local scopeText = ""
local alerted, replied = {}, {}
local lastManualSync = 0

local net = {
  addonRx = false, chatRx = false,         -- which transports have been proven to deliver
  tx = 0, rx = 0, dropped = 0,
  lastRx = 0, lastRxKind = "", lastDist = "",
  lastResult = "-", lastChatResult = "-",
  peers = {}, seen = {},
  announced = false, lastJoin = 0, enterTime = 0,
  lastDumpHeard = 0, lastDumpSent = 0, lastQReply = 0, lastPHeard = 0, lastPSent = 0,
  dumpPending = false, rejected = 0,
}

local f = CreateFrame("Frame")

---------------------------------------------------------------------------
-- Helpers
---------------------------------------------------------------------------
local function msg(t) print("|cff69ccf0[MageBL]|r " .. t) end

local function secret(v) return issecretvalue and issecretvalue(v) end

local function trim(s)
  s = string.gsub(s or "", "^%s+", "")
  s = string.gsub(s, "%s+$", "")
  return s
end

local function clean(s)
  s = string.gsub(s or "", "[~%^|%c]", " ")
  return s
end

local function cap(s)
  s = string.gsub(s, "(%a)([^%s]*)", function(a, b) return string.upper(a) .. string.lower(b) end)
  return s
end

-- WoW Forever: a character is "First Surname". Events may deliver "First-Surname" or "First Surname".
local function normName(n)
  if not n or n == "" then return "" end
  n = string.gsub(n, "%s+", " ")
  if string.find(n, " ", 1, true) then
    n = string.gsub(n, "%-.*$", "")      -- "First Surname-Realm" -> cut the tail
  else
    n = string.gsub(n, "%-", " ")        -- "First-Surname" -> "First Surname"
  end
  n = trim(n)
  local a, b = string.match(n, "^(%S+)%s+(%S+)")
  if a then n = a .. " " .. b end         -- never more than first name + surname
  return n
end
local shortName = normName

-- Same character? Tolerates one side having lost its surname.
local function sameChar(a, b)
  a, b = string.lower(normName(a)), string.lower(normName(b))
  if a == "" or b == "" then return false end
  if a == b then return true end
  local fa, fb = string.match(a, "^(%S+)"), string.match(b, "^(%S+)")
  if fa == fb and (not string.find(a, " ", 1, true) or not string.find(b, " ", 1, true)) then return true end
  return false
end

local function split(s, sep)
  local t, n, pos = {}, 0, 1
  while true do
    local a = string.find(s, sep, pos, true)
    if not a then n = n + 1; t[n] = string.sub(s, pos); break end
    n = n + 1; t[n] = string.sub(s, pos, a - 1); pos = a + 1
  end
  return t, n
end

local function now() return GetServerTime() end

local function locked()
  return C_ChatInfo and C_ChatInfo.InChatMessagingLockdown and C_ChatInfo.InChatMessagingLockdown()
end

-- full name of a unit: first name + surname (UnitName returns the surname in the 2nd slot on Forever)
local function unitFull(unit)
  local n, sur = (UnitNameUnmodified or UnitName)(unit)
  if not n or secret(n) then return nil end
  if sur and not secret(sur) and sur ~= "" then n = n .. " " .. sur end
  return n
end

---------------------------------------------------------------------------
-- Eligibility: Mage, level 20+
---------------------------------------------------------------------------
local function eligible()
  local _, class = UnitClass("player")
  return class == "MAGE" and (UnitLevel("player") or 0) >= MIN_LEVEL
end

local function refuse() msg("This addon only works for Mages level " .. MIN_LEVEL .. " and above.") end

---------------------------------------------------------------------------
-- Channel / peers / status
---------------------------------------------------------------------------
local function chanId()
  local id = GetChannelName(CHANNEL)
  return id or 0
end

local function touchPeer(sender, how)
  local key = string.lower(normName(sender))
  if key == "" then return false end
  local t, p = GetTime(), net.peers[key]
  local fresh = (not p) or (t - p.t > PEER_TTL)
  if not p then
    p = { name = normName(sender), t = t }
    net.peers[key] = p
  end
  p.t = t
  if how == "chan" then p.chanT = t end
  return fresh
end

-- true if this mage talks to us through the shared channel (then no direct whispers are needed)
local function reachableByChannel(key)
  local p = net.peers[key]
  return p and p.chanT and (GetTime() - p.chanT) < PEER_TTL
end

local function peerCount()
  local t, n = GetTime(), 0
  for k, p in pairs(net.peers) do
    if t - p.t > PEER_TTL then net.peers[k] = nil else n = n + 1 end
  end
  return n
end

local function status()
  if not enabled then return "off", "Inactive - Mages level " .. MIN_LEVEL .. "+ only" end
  if chanId() == 0 then return "wait", "Connecting to the sync channel..." end
  local n = peerCount()
  if n == 0 then return "idle", "Connected - no other mages seen yet" end
  return "ok", "Synced - " .. n .. (n == 1 and " other mage" or " other mages") .. " online"
end

---------------------------------------------------------------------------
-- Sending: queue -> addon message (+ chat fallback), results are checked
---------------------------------------------------------------------------
local queue, qh, qt = {}, 1, 0      -- messages for the shared channel
local wq, wh, wt = {}, 1, 0         -- direct messages (whisper / guild addon messages)

-- always: also use the chat fallback (live changes); otherwise only until addon messages proved to work
local function send(text, always)
  qt = qt + 1
  queue[qt] = { t = text, always = always, tries = 0 }
end

local function sendTo(name, text)
  name = normName(name)
  if name == "" or (wt - wh) > 300 then return end
  wt = wt + 1
  wq[wt] = { t = text, dist = "WHISPER", to = name, tries = 0 }
end

local function sendGuild(text)
  if (wt - wh) > 300 then return end
  wt = wt + 1
  wq[wt] = { t = text, dist = "GUILD", tries = 0 }
end

local SR = Enum and Enum.SendAddonMessageResult
local function classify(r)
  if r == nil or r == true or r == 0 then return "ok" end
  if SR then
    if r == SR.Success then return "ok" end
    if r == SR.AddonMessageThrottle or r == SR.ChannelThrottle or r == SR.ChatThrottled then return "throttle" end
  end
  if r == 3 or r == 8 then return "throttle" end
  return "fail"
end

local function transmit(it, id)
  local aStat, cStat = "none", "none"
  local dual = it.always or not net.addonRx

  local fn = (C_ChatInfo and C_ChatInfo.SendAddonMessage) or SendAddonMessage
  if fn then
    local ok, r = pcall(fn, PREFIX, it.t, "CHANNEL", id)
    if ok then
      aStat = classify(r)
      net.lastResult = tostring(r == nil and "ok" or r)
    else
      aStat = "fail"
      net.lastResult = "error: " .. tostring(r)
    end
  end

  if dual and not it.chatDone then
    local cfn = SendChatMessage or (C_ChatInfo and C_ChatInfo.SendChatMessage)
    if cfn then
      local ok, err = pcall(cfn, CHAT_TAG .. it.t, "CHANNEL", nil, id)
      cStat = ok and "ok" or "fail"
      net.lastChatResult = ok and "ok" or ("error: " .. tostring(err))
      if ok then it.chatDone = true end
    end
  end

  if aStat == "ok" or cStat == "ok" or it.chatDone then return "ok" end
  if aStat == "throttle" then return "retry" end
  return "fail"
end

local function transmitDirect(it)
  local fn = (C_ChatInfo and C_ChatInfo.SendAddonMessage) or SendAddonMessage
  if not fn then return "fail" end
  local ok, r = pcall(fn, PREFIX, it.t, it.dist, it.to)
  if not ok then net.lastWResult = "error: " .. tostring(r); return "fail" end
  net.lastWResult = tostring(r == nil and "ok" or r)
  return classify(r)
end

local backoffUntil, turn = 0, 0
C_Timer.NewTicker(0.8, function()
  if not enabled then return end
  if GetTime() < backoffUntil or locked() then return end
  turn = turn + 1

  -- direct messages (links / guild), alternating with the channel queue
  if wh <= wt and (qh > qt or turn % 2 == 0) then
    local it = wq[wh]
    local r = transmitDirect(it)
    if r == "retry" then
      it.tries = it.tries + 1
      if it.tries <= 8 then backoffUntil = GetTime() + 2.5; return end
      net.dropped = net.dropped + 1
    elseif r == "fail" then
      if it.dist == "WHISPER" and not it.alt then
        it.alt = true                       -- try the "First-Surname" spelling once
        it.to = (string.gsub(it.to, " ", "-"))
        return
      end
      net.dropped = net.dropped + 1         -- offline / unknown target
    else
      net.tx = net.tx + 1
    end
    wq[wh] = nil
    wh = wh + 1
    if wh > wt then wq, wh, wt = {}, 1, 0 end
    return
  end

  if qh > qt then return end
  local id = chanId()
  if id <= 0 then return end
  local it = queue[qh]
  local r = transmit(it, id)
  if r == "retry" then
    it.tries = it.tries + 1
    if it.tries <= 8 then backoffUntil = GetTime() + 2.5; return end
    net.dropped = net.dropped + 1
  elseif r == "fail" then
    it.tries = it.tries + 1
    if it.tries <= 3 then backoffUntil = GetTime() + 2; return end
    net.dropped = net.dropped + 1
  else
    net.tx = net.tx + 1
  end
  queue[qh] = nil
  qh = qh + 1
  if qh > qt then queue, qh, qt = {}, 1, 0 end
end)

---------------------------------------------------------------------------
-- Direct links (work across backend realms)
---------------------------------------------------------------------------
local function addLink(name, manual)
  name = normName(name)
  if name == "" or sameChar(name, me) then return false end
  S.links = S.links or {}
  local k = string.lower(name)
  local l = S.links[k]
  if l then
    l.t = now()
    if manual then l.manual = true end
    return false
  end
  local n = 0
  for _ in pairs(S.links) do n = n + 1 end
  if n >= MESH_MAX then
    local oldK, oldT
    for kk, ll in pairs(S.links) do
      if not ll.manual and (not oldT or ll.t < oldT) then oldK, oldT = kk, ll.t end
    end
    if not oldK then return false end
    S.links[oldK] = nil
  end
  S.links[k] = { name = name, manual = manual and true or false, t = now() }
  return true
end

-- send to every direct link that is NOT already reachable through the shared channel
local function forwardToLinks(text, exceptKey)
  if not S or not S.links then return end
  for k, l in pairs(S.links) do
    if k ~= exceptKey and not reachableByChannel(k) then sendTo(l.name, text) end
  end
end

---------------------------------------------------------------------------
-- Records
---------------------------------------------------------------------------
local function rec(e)
  return e.name .. FS .. e.owner .. FS .. e.time .. FS .. e.ver .. FS .. (e.active and "1" or "0") .. FS .. (e.reason or "")
end

-- true if "n" should replace the existing record "old"
local function better(n, old)
  if not old then return true end
  if n.owner == old.owner then return n.ver > old.ver end
  if n.active and not old.active then return true end
  if n.active and old.active then
    if n.time ~= old.time then return n.time < old.time end
    return n.owner < old.owner
  end
  if (not n.active) and (not old.active) then return n.ver > old.ver end
  return false -- nobody else can remove another mage's record
end

local function checksum()
  local sum, cnt = 0, 0
  for k, e in pairs(DB) do
    cnt = cnt + 1
    local s = k .. e.owner .. tostring(e.ver) .. (e.active and "1" or "0")
    local h = 0
    for i = 1, #s do h = (h * 31 + string.byte(s, i)) % 1000003 end
    sum = (sum + h) % 1000000007
  end
  return sum, cnt
end

local updateUI, updateMinimap

local function queryText()
  local sum, cnt = checksum()
  return "Q" .. FS .. sum .. FS .. cnt
end

local function presenceText()
  local _, cnt = checksum()
  return "P" .. FS .. VERSION .. FS .. cnt
end

local function sendQuery() send(queryText()) end

local function sendPresence()
  if GetTime() - net.lastPSent < 15 then return end
  net.lastPSent = GetTime()
  send(presenceText())
end

local function emit(text, to) if to then sendTo(to, text) else send(text) end end

-- to == nil -> shared channel, otherwise a direct whisper to that mage
local function dump(onlyMine, to)
  local cur = "D"
  for k, e in pairs(DB) do
    if (not onlyMine) or e.owner == me then
      local r = rec(e)
      if #cur + 1 + #r > 225 then emit(cur, to); cur = "D" end
      cur = cur .. RS .. r
    end
  end
  if cur ~= "D" then emit(cur, to) end
end

local function packRecords(list)
  local out, cur = {}, "D"
  for _, r in ipairs(list) do
    if #cur + 1 + #r > 225 then out[#out + 1] = cur; cur = "D" end
    cur = cur .. RS .. r
  end
  if cur ~= "D" then out[#out + 1] = cur end
  return out
end

-- probability that this client answers (keeps big groups from all answering at once)
local function answerChance()
  local n = peerCount()
  if n <= 3 then return 1 end
  return 3 / n
end

local function scheduleDump()
  if net.dumpPending then return end
  net.dumpPending = true
  local t0 = GetTime()
  C_Timer.After(2 + math.random() * 7, function()
    net.dumpPending = false
    if net.lastDumpHeard > t0 then return end            -- somebody else is already sending the list
    if GetTime() - net.lastDumpSent < 45 then return end
    net.lastDumpSent = GetTime()
    dump(false)
  end)
end

local function onMessage(text, sender, fresh, via)
  local kind = string.sub(text, 1, 1)
  local direct = (via == "whisper" or via == "guild")
  local skey = string.lower(normName(sender))

  if kind == "Q" then
    local fld = split(text, FS)
    local theirs = tonumber(fld[2])
    local mine = checksum()
    if direct then
      if reachableByChannel(skey) then return end      -- we already sync with them through the channel
      local p = net.peers[skey]
      if theirs ~= mine then
        if p and GetTime() - (p.dumpT or 0) > 30 then
          p.dumpT = GetTime()
          C_Timer.After(1, function()
            dump(false, sender)
            sendTo(sender, queryText())
          end)
        end
      elseif fresh then
        sendTo(sender, presenceText())                  -- say hello, so they see that the link works
      end
    else
      if theirs ~= mine then
        if math.random() < answerChance() then
          scheduleDump()
          -- tell the other side we differ, so they send their list too
          if GetTime() - net.lastQReply > 20 then
            net.lastQReply = GetTime()
            C_Timer.After(1 + math.random() * 3, sendQuery)
          end
        end
      elseif fresh and math.random() < answerChance() then
        -- a new mage appeared and our lists match: just say hello so they see that we exist
        local t0 = GetTime()
        C_Timer.After(1 + math.random() * 8, function()
          if net.lastPHeard > t0 and peerCount() > 3 then return end
          sendPresence()
        end)
      end
      if fresh and theirs ~= mine then
        C_Timer.After(1 + math.random() * 6, function() sendPresence() end)
      end
    end

  elseif kind == "P" then
    net.lastPHeard = GetTime()
    local fld = split(text, FS)
    local p = net.peers[skey]
    if p then p.ver = fld[2] end

  elseif kind == "E" or kind == "D" then
    local recs, n = split(text, RS)
    if kind == "D" and not direct then net.lastDumpHeard = GetTime() end
    local accepted, changes = {}, {}
    for i = 2, n do
      local x = split(recs[i], FS)
      local name  = normName(trim(clean(x[1])))
      local owner = normName(x[2] or "")
      local tm, ver = tonumber(x[3]), tonumber(x[4])
      local active = (x[5] == "1")
      if name ~= "" and #name <= 40 and owner ~= "" and #owner <= 60 and tm and ver then
        -- a live REMOVAL may only come from the mage who owns the record
        local allowed = true
        if kind == "E" and (not active) and not sameChar(owner, sender) then
          allowed = false
          net.rejected = net.rejected + 1
        end
        if allowed then
          local key = string.lower(name)
          local e = { name = name, owner = owner, time = tm, ver = ver,
                      active = active, reason = string.sub(clean(x[6] or ""), 1, 60) }
          if better(e, DB[key]) then
            DB[key] = e
            accepted[#accepted + 1] = rec(e)
            changes[#changes + 1] = e
          end
        end
      end
    end
    if #accepted > 0 then
      if S.notify ~= false and (kind == "E" or #changes <= 3) then
        for _, e in ipairs(changes) do
          if e.active then
            msg(e.owner .. " added to blacklist: " .. e.name)
          else
            msg(e.owner .. " removed from blacklist: " .. e.name)
          end
        end
      end
      -- relay, so mages on different backend realms (bridged by direct links) stay in sync
      for _, one in ipairs(packRecords(accepted)) do
        if direct then send(one) end         -- hand it on to my own shared channel
        forwardToLinks(one, skey)            -- ... and to my other direct links
      end
      updateUI()
    end
  end
end

-- entry point for everything that arrives (addon message, chat fallback, whisper, guild)
local function handle(text, sender, via)
  if not text or not sender or secret(text) or secret(sender) then return end
  if sameChar(sender, me) then return end
  net.rx = net.rx + 1
  net.lastRx = GetTime()
  net.lastRxKind = string.sub(text, 1, 1)
  local direct = (via == "whisper" or via == "guild")
  if via == "addon" then net.addonRx = true elseif via == "chat" then net.chatRx = true end

  local key = normName(sender) .. "\1" .. text
  local t = GetTime()
  if net.seen[key] and t - net.seen[key] < 20 then return end   -- same message via another transport
  net.seen[key] = t

  local fresh = touchPeer(sender, direct and "direct" or "chan")
  if direct then
    local sk = string.lower(normName(sender))
    if not reachableByChannel(sk) then
      addLink(sender, false)                 -- they reached us directly: link back automatically
      local l = S.links and S.links[sk]
      if l then l.t = now() end
    end
  end
  onMessage(text, sender, fresh, via)
end

---------------------------------------------------------------------------
-- Add / remove
---------------------------------------------------------------------------
local function addEntry(name, reason)
  if not enabled then refuse() return end
  name = cap(normName(trim(clean(name))))
  if name == "" then msg("Enter a player name.") return end
  name = string.sub(name, 1, 40)
  local key = string.lower(name)
  if key == string.lower(myShort) then msg("You can't blacklist yourself.") return end
  local old = DB[key]
  if old and old.active then
    msg(old.name .. " is already blacklisted (added by " .. old.owner .. ").")
    return
  end
  local t = now()
  local ver = t
  if old and ver <= old.ver then ver = old.ver + 1 end
  local e = { name = name, owner = me, time = t, ver = ver, active = true,
              reason = string.sub(clean(trim(reason or "")), 1, 60) }
  DB[key] = e
  send("E" .. RS .. rec(e), true)
  forwardToLinks("E" .. RS .. rec(e))
  local n = peerCount()
  if n > 0 then
    msg(name .. " added to the blacklist and shared with " .. n .. (n == 1 and " online mage." or " online mages."))
  else
    msg(name .. " added to the blacklist. No other mages seen online right now - they will get it when they sync.")
  end
  updateUI()
end

local function removeEntry(name)
  if not enabled then refuse() return end
  name = normName(trim(name or ""))
  local key = string.lower(name)
  local e = DB[key]
  if not e or not e.active then msg("Player '" .. name .. "' is not on the blacklist.") return end
  if e.owner ~= me then
    msg("Only " .. e.owner .. " (who added this player) can remove the entry.")
    return
  end
  e.active = false
  local v = now()
  if v <= e.ver then v = e.ver + 1 end
  e.ver = v
  send("E" .. RS .. rec(e), true)
  forwardToLinks("E" .. RS .. rec(e))
  msg(e.name .. " removed from the blacklist.")
  updateUI()
end

local function isBlack(name)
  if not name or secret(name) then return nil end
  local e = DB and DB[string.lower(normName(name))]
  if e and e.active then return e end
end

---------------------------------------------------------------------------
-- Warnings / ignoring / auto-reply
---------------------------------------------------------------------------
local function alert(name, why)
  if not enabled then return end
  local e = isBlack(name)
  if not e then return end
  local key = string.lower(e.name)
  if alerted[key] and GetTime() - alerted[key] < 60 then return end
  alerted[key] = GetTime()
  local txt = "BLACKLIST: " .. e.name .. " (" .. why .. ") did not pay for a portal! Added by: " .. e.owner ..
              ((e.reason and e.reason ~= "") and (" - " .. e.reason) or "")
  msg("|cffff3030" .. txt .. "|r")
  if UIErrorsFrame then UIErrorsFrame:AddMessage(txt, 1, 0.15, 0.15, 1, 6) end
  if SOUNDKIT and PlaySound then PlaySound(SOUNDKIT.RAID_WARNING) end
end

local function whisperFilter(self, event, text, author)
  if not enabled or not S or S.mode ~= "ignore" then return end
  if secret(author) or secret(text) then return end
  if isBlack(author) then return true end -- message is hidden
end
ChatFrame_AddMessageEventFilter("CHAT_MSG_WHISPER", whisperFilter)

local function chanNoiseFilter(self, event, a1, a2, a3, a4, a5, a6, a7, a8, a9)
  if not secret(a4) and a4 and string.find(string.lower(a4), string.lower(CHANNEL_BASE), 1, true) then return true end
  if not secret(a9) and a9 and string.find(string.lower(a9), string.lower(CHANNEL_BASE), 1, true) then return true end
end
for _, ev in ipairs({ "CHAT_MSG_CHANNEL_NOTICE", "CHAT_MSG_CHANNEL_NOTICE_USER", "CHAT_MSG_CHANNEL_JOIN",
                      "CHAT_MSG_CHANNEL_LEAVE", "CHAT_MSG_CHANNEL" }) do
  ChatFrame_AddMessageEventFilter(ev, chanNoiseFilter)
end

local function formatReply(tpl, e)
  tpl = tpl or DEFAULT_REPLY
  tpl = string.gsub(tpl, "{player}", function() return e.name end)
  tpl = string.gsub(tpl, "{owner}",  function() return e.owner end)
  tpl = string.gsub(tpl, "{reason}", function() return (e.reason and e.reason ~= "") and e.reason or "unpaid portal" end)
  return string.sub(tpl, 1, 255)
end

local function onWhisper(text, author)
  if not enabled or secret(author) or secret(text) then return end
  local e = isBlack(author)
  if not e then return end
  if S.mode == "ignore" then
    local key = string.lower(e.name)
    if not alerted[key] or GetTime() - alerted[key] > 60 then
      alerted[key] = GetTime()
      msg("Ignoring whisper from " .. e.name .. " (blacklisted by " .. e.owner .. ").")
    end
  else
    alert(author, "is whispering you")
  end
  if S.autoreply and not locked() then
    local key = string.lower(e.name)
    if not replied[key] or GetTime() - replied[key] > 600 then
      replied[key] = GetTime()
      local send_ = (C_ChatInfo and C_ChatInfo.SendChatMessage) or SendChatMessage
      send_(formatReply(S.replytext, e), "WHISPER", nil, author)
    end
  end
end

---------------------------------------------------------------------------
-- UI toolkit (flat dark "arcane" theme)
---------------------------------------------------------------------------
-- Portal icon of your faction taken from the spell itself (works even if the file path is unknown)
local function iconTexture()
  local spell = (UnitFactionGroup and UnitFactionGroup("player") == "Horde") and 11417 or 10059
  if C_Spell and C_Spell.GetSpellTexture then
    local ok, t = pcall(C_Spell.GetSpellTexture, spell)
    if ok and t then return t end
  end
  if GetSpellTexture then
    local ok, t = pcall(GetSpellTexture, spell)
    if ok and t then return t end
  end
  return ICON
end

local BD = BackdropTemplateMixin and "BackdropTemplate" or nil

local C = {
  bg      = { 0.045, 0.038, 0.095, 0.97 },
  header  = { 0.085, 0.060, 0.190, 1 },
  panel   = { 0.075, 0.065, 0.150, 1 },
  row1    = { 0.085, 0.075, 0.170, 1 },
  row2    = { 0.065, 0.055, 0.135, 1 },
  rowHot  = { 0.140, 0.115, 0.290, 1 },
  input   = { 0.030, 0.026, 0.070, 1 },
  btn     = { 0.200, 0.160, 0.440, 1 },
  accentB = { 0.120, 0.480, 0.640, 1 },
  danger  = { 0.560, 0.150, 0.220, 1 },
  on      = { 0.180, 0.620, 0.400, 1 },
  off     = { 0.220, 0.200, 0.330, 1 },
  border  = { 0.330, 0.270, 0.700, 1 },
  clear   = { 0, 0, 0, 0 },
  accent  = { 0.40, 0.88, 1.00, 1 },
  white   = { 0.95, 0.95, 1.00, 1 },
  muted   = { 0.62, 0.60, 0.80, 1 },
  gold    = { 1.00, 0.82, 0.30, 1 },
  green   = { 0.30, 0.90, 0.50, 1 },
  orange  = { 1.00, 0.65, 0.20, 1 },
  red     = { 1.00, 0.30, 0.35, 1 },
}

local function skin(fr, bgc, bdc)
  if fr.SetBackdrop then
    fr:SetBackdrop({ bgFile = WHITE, edgeFile = WHITE, edgeSize = 1,
                     insets = { left = 1, right = 1, top = 1, bottom = 1 } })
    fr:SetBackdropColor(bgc[1], bgc[2], bgc[3], bgc[4] or 1)
    fr:SetBackdropBorderColor(bdc[1], bdc[2], bdc[3], bdc[4] or 1)
  end
end

local function lighten(c, d)
  return { math.min(1, c[1] + d), math.min(1, c[2] + d), math.min(1, c[3] + d), c[4] or 1 }
end

local function mkText(parent, font, color)
  local fs = parent:CreateFontString(nil, "OVERLAY", font or "GameFontHighlightSmall")
  if color then fs:SetTextColor(color[1], color[2], color[3], color[4] or 1) end
  fs:SetJustifyH("LEFT")
  return fs
end

local function mkButton(parent, text, w, h, col, border)
  col = col or C.btn
  local b = CreateFrame("Button", nil, parent, BD)
  b:SetSize(w, h)
  b.base, b.hover = col, lighten(col, 0.13)
  skin(b, col, border or C.border)
  b.text = mkText(b, "GameFontHighlightSmall", C.white)
  b.text:SetJustifyH("CENTER")
  b.text:SetPoint("CENTER", 0, 0)
  b.text:SetText(text)
  b:SetScript("OnEnter", function(s) if s.SetBackdropColor then s:SetBackdropColor(s.hover[1], s.hover[2], s.hover[3], 1) end end)
  b:SetScript("OnLeave", function(s) if s.SetBackdropColor then s:SetBackdropColor(s.base[1], s.base[2], s.base[3], 1) end end)
  return b
end

local function mkEdit(parent, w, h, hint, maxLetters)
  local e = CreateFrame("EditBox", nil, parent, BD)
  e:SetSize(w, h)
  e:SetAutoFocus(false)
  e:SetMaxLetters(maxLetters or 60)
  e:SetFontObject("GameFontHighlightSmall")
  e:SetTextInsets(8, 8, 0, 0)
  skin(e, C.input, C.border)
  e.hint = mkText(e, "GameFontHighlightSmall", { 0.45, 0.43, 0.62, 1 })
  e.hint:SetPoint("LEFT", 8, 0)
  e.hint:SetText(hint or "")
  local function upd(s)
    if s:GetText() == "" and not s:HasFocus() then s.hint:Show() else s.hint:Hide() end
  end
  e:SetScript("OnEditFocusGained", function(s)
    if s.SetBackdropBorderColor then s:SetBackdropBorderColor(C.accent[1], C.accent[2], C.accent[3], 1) end
    upd(s)
  end)
  e:SetScript("OnEditFocusLost", function(s)
    if s.SetBackdropBorderColor then s:SetBackdropBorderColor(C.border[1], C.border[2], C.border[3], 1) end
    upd(s)
  end)
  e:SetScript("OnTextChanged", function(s, user)
    upd(s)
    if s.onChange then s.onChange(s, user) end
  end)
  e:SetScript("OnEscapePressed", function(s) s:ClearFocus() end)
  return e
end

local function mkToggle(parent, label, hint, get, set)
  local row = CreateFrame("Button", nil, parent)
  row:SetSize(476, 36)
  local lbl = mkText(row, "GameFontHighlight", C.white)
  lbl:SetPoint("TOPLEFT", 0, -2)
  lbl:SetText(label)
  local hnt = mkText(row, "GameFontHighlightSmall", C.muted)
  hnt:SetPoint("BOTTOMLEFT", 0, 2)
  hnt:SetText(hint)
  local pill = CreateFrame("Frame", nil, row, BD)
  pill:SetSize(40, 20)
  pill:SetPoint("RIGHT", 0, 0)
  local knob = pill:CreateTexture(nil, "OVERLAY")
  knob:SetSize(14, 14)
  knob:SetColorTexture(1, 1, 1, 1)
  function row:Refresh()
    local on = get() and true or false
    skin(pill, on and C.on or C.off, C.border)
    knob:ClearAllPoints()
    knob:SetPoint(on and "RIGHT" or "LEFT", on and -3 or 3, 0)
  end
  row:SetScript("OnClick", function() set(not get()); row:Refresh(); updateUI() end)
  return row
end

-- round colored status dot
local function mkDot(parent, size)
  local t = parent:CreateTexture(nil, "OVERLAY")
  t:SetSize(size, size)
  t:SetColorTexture(1, 1, 1, 1)
  if parent.CreateMaskTexture then
    local m = parent:CreateMaskTexture()
    m:SetTexture("Interface\\CharacterFrame\\TempPortraitAlphaMask", "CLAMPTOBLACKADDITIVE", "CLAMPTOBLACKADDITIVE")
    m:SetAllPoints(t)
    t:AddMaskTexture(m)
  end
  function t:SetState(st)
    local c = (st == "ok" and C.green) or (st == "idle" and C.orange) or (st == "wait" and C.orange) or C.red
    self:SetColorTexture(c[1], c[2], c[3], 1)
  end
  return t
end

---------------------------------------------------------------------------
-- Main window
---------------------------------------------------------------------------
local ui
local page, tab = 1, 1

local function sortedList()
  local filter = ""
  if ui and ui.filter then filter = string.lower(trim(ui.filter:GetText() or "")) end
  local list = {}
  for _, e in pairs(DB) do
    if e.active then
      if filter == "" or string.find(string.lower(e.name), filter, 1, true)
         or string.find(string.lower(e.owner), filter, 1, true) then
        list[#list + 1] = e
      end
    end
  end
  table.sort(list, function(a, b) return string.lower(a.name) < string.lower(b.name) end)
  return list
end

local function ago(sec)
  if sec < 2 then return "just now" end
  if sec < 90 then return math.floor(sec) .. "s ago" end
  if sec < 5400 then return math.floor(sec / 60) .. "m ago" end
  return math.floor(sec / 3600) .. "h ago"
end

local function refreshStatus()
  local st, text = status()
  if ui then
    ui.dot:SetState(st)
    ui.statusText:SetText(text)
    local t = GetTime()
    ui.scopeLine:SetText("|cff9d9acfBackend realm:|r " .. scopeText .. "   |cff9d9acf(channel reaches mages on the same one)|r")
    local nl, nr = 0, 0
    if S and S.links then
      for k in pairs(S.links) do nl = nl + 1; if reachableByChannel(k) then nr = nr + 1 end end
    end
    ui.linkLine:SetText("|cff9d9acfDirect links:|r " .. nl .. (nl > 0 and ("  (" .. (nl - nr) .. " bridged by whisper)") or ""))
    ui.peerLine:SetText("|cff9d9acfMages online:|r " .. peerCount())
    ui.rxLine:SetText("|cff9d9acfLast message:|r " .. (net.lastRx > 0 and ago(t - net.lastRx) or "none yet"))
    ui.txLine:SetText("|cff9d9acfTransport:|r " .. (net.addonRx and "addon messages" or "addon messages + chat fallback")
                      .. "   |cff9d9acfSent:|r " .. net.tx .. "   |cff9d9acfReceived:|r " .. net.rx)
  end
  if updateMinimap then updateMinimap() end
end

updateUI = function()
  if not ui or not ui:IsShown() then return end
  local list = sortedList()
  local total = #list
  local pages = math.max(1, math.ceil(total / ROWS))
  page = math.min(math.max(page, 1), pages)
  for i = 1, ROWS do
    local e = list[(page - 1) * ROWS + i]
    local row = ui.rows[i]
    if e then
      row.entry = e
      row.name:SetText(e.name)
      local r = e.reason or ""
      if #r > 38 then r = string.sub(r, 1, 38) .. ".." end
      row.info:SetText("added by " .. e.owner .. "  -  " .. date("%b %d", e.time) .. ((r ~= "") and ("  -  " .. r) or ""))
      row.key = string.lower(e.name)
      if e.owner == me then
        row.btn:Show(); row.locked:Hide()
      else
        row.btn:Hide(); row.locked:Show()
      end
      row:Show()
    else
      row.entry = nil
      row:Hide()
    end
  end
  ui.empty:SetShown(total == 0)
  ui.countText:SetText("Blacklisted players: |cffffffff" .. total .. "|r")
  ui.pageText:SetText("Page " .. page .. " / " .. pages)
  ui.tglIgnore:Refresh()
  ui.tglReply:Refresh()
  ui.tglMinimap:Refresh()
  ui.tglNotify:Refresh()
  refreshStatus()
end

local function selectTab(n)
  tab = n
  ui.pageList:SetShown(n == 1)
  ui.pageSet:SetShown(n == 2)
  for i = 1, 2 do
    local b = ui.tabs[i]
    local on = (i == n)
    b.base = on and C.btn or C.panel
    b.hover = lighten(b.base, 0.1)
    skin(b, b.base, on and C.accent or C.border)
    b.text:SetTextColor(on and 1 or 0.7, on and 1 or 0.7, 1, 1)
  end
end

local function buildUI()
  if ui then return end
  ui = CreateFrame("Frame", "MageBlacklistFrame", UIParent, BD)
  ui:SetSize(500, 624)
  ui:SetPoint("CENTER")
  ui:SetFrameStrata("HIGH")
  ui:SetMovable(true)
  ui:EnableMouse(true)
  ui:SetClampedToScreen(true)
  ui:RegisterForDrag("LeftButton")
  ui:SetScript("OnDragStart", function(s) s:StartMoving() end)
  ui:SetScript("OnDragStop", function(s) s:StopMovingOrSizing() end)
  skin(ui, C.bg, C.border)
  tinsert(UISpecialFrames, "MageBlacklistFrame")

  -- header ---------------------------------------------------------------
  local header = CreateFrame("Frame", nil, ui, BD)
  header:SetPoint("TOPLEFT", 1, -1)
  header:SetPoint("TOPRIGHT", -1, -1)
  header:SetHeight(56)
  skin(header, C.header, C.header)

  local iconBox = CreateFrame("Frame", nil, header, BD)
  iconBox:SetSize(38, 38)
  iconBox:SetPoint("LEFT", 14, 0)
  skin(iconBox, C.input, C.accent)
  local icon = iconBox:CreateTexture(nil, "ARTWORK")
  icon:SetPoint("TOPLEFT", 2, -2)
  icon:SetPoint("BOTTOMRIGHT", -2, 2)
  icon:SetTexture(iconTexture())
  ui.icon = icon
  icon:SetTexCoord(0.07, 0.93, 0.07, 0.93)

  local title = mkText(header, "GameFontNormalLarge", C.accent)
  title:SetPoint("TOPLEFT", iconBox, "TOPRIGHT", 12, -1)
  title:SetText("Mage Portal Blacklist")
  local sub = mkText(header, "GameFontHighlightSmall", C.muted)
  sub:SetPoint("BOTTOMLEFT", iconBox, "BOTTOMRIGHT", 12, 1)
  sub:SetText("Shared list of portal non-payers  -  v" .. VERSION)

  local close = mkButton(header, "X", 24, 24, C.btn)
  close:SetPoint("TOPRIGHT", -10, -10)
  close:SetScript("OnClick", function() ui:Hide() end)

  local line = ui:CreateTexture(nil, "ARTWORK")
  line:SetColorTexture(C.accent[1], C.accent[2], C.accent[3], 0.55)
  line:SetPoint("TOPLEFT", header, "BOTTOMLEFT", 0, 0)
  line:SetPoint("TOPRIGHT", header, "BOTTOMRIGHT", 0, 0)
  line:SetHeight(1)

  -- tabs -------------------------------------------------------------------
  ui.tabs = {}
  local names = { "Blacklist", "Settings & Sync" }
  local widths = { 110, 140 }
  local x = 12
  for i = 1, 2 do
    local b = mkButton(ui, names[i], widths[i], 26, C.panel)
    b:SetPoint("TOPLEFT", x, -64)
    b:SetScript("OnClick", function() selectTab(i); updateUI() end)
    ui.tabs[i] = b
    x = x + widths[i] + 6
  end

  -- footer (status) --------------------------------------------------------
  local footer = CreateFrame("Frame", nil, ui, BD)
  footer:SetPoint("BOTTOMLEFT", 1, 1)
  footer:SetPoint("BOTTOMRIGHT", -1, 1)
  footer:SetHeight(28)
  skin(footer, C.header, C.header)
  ui.dot = mkDot(footer, 10)
  ui.dot:SetPoint("LEFT", 14, 0)
  ui.statusText = mkText(footer, "GameFontHighlightSmall", C.white)
  ui.statusText:SetPoint("LEFT", ui.dot, "RIGHT", 8, 0)
  local hintR = mkText(footer, "GameFontHighlightSmall", C.muted)
  hintR:SetPoint("RIGHT", -12, 0)
  hintR:SetText("Mage level " .. MIN_LEVEL .. "+")

  -- page 1: blacklist ------------------------------------------------------
  local p1 = CreateFrame("Frame", nil, ui)
  p1:SetPoint("TOPLEFT", 12, -98)
  p1:SetPoint("BOTTOMRIGHT", -12, 36)
  ui.pageList = p1

  local nameBox = mkEdit(p1, 170, 26, "Player name (First Surname)", 40)
  nameBox:SetPoint("TOPLEFT", 0, 0)
  local reasonBox = mkEdit(p1, 150, 26, "Reason (optional)", 60)
  reasonBox:SetPoint("LEFT", nameBox, "RIGHT", 6, 0)
  local function doAdd()
    addEntry(nameBox:GetText(), reasonBox:GetText())
    nameBox:SetText(""); reasonBox:SetText("")
    nameBox:ClearFocus(); reasonBox:ClearFocus()
  end
  nameBox:SetScript("OnEnterPressed", doAdd)
  reasonBox:SetScript("OnEnterPressed", doAdd)

  local targetBtn = mkButton(p1, "Target", 60, 26, C.btn)
  targetBtn:SetPoint("LEFT", reasonBox, "RIGHT", 6, 0)
  targetBtn:SetScript("OnClick", function()
    if UnitExists("target") and UnitIsPlayer("target") and not UnitIsUnit("target", "player") then
      local n = unitFull("target")
      if n then nameBox:SetText(n) return end
    end
    msg("Select another player as your target first.")
  end)
  local addBtn = mkButton(p1, "Add", 70, 26, C.accentB, C.accent)
  addBtn:SetPoint("LEFT", targetBtn, "RIGHT", 6, 0)
  addBtn:SetScript("OnClick", doAdd)

  ui.countText = mkText(p1, "GameFontHighlight", C.muted)
  ui.countText:SetPoint("TOPLEFT", 2, -40)
  ui.filter = mkEdit(p1, 150, 22, "Search...", 40)
  ui.filter:SetPoint("TOPRIGHT", 0, -36)
  ui.filter.onChange = function() page = 1; updateUI() end

  ui.rows = {}
  for i = 1, ROWS do
    local row = CreateFrame("Button", nil, p1, BD)
    row:SetSize(476, 36)
    row:SetPoint("TOPLEFT", 0, -64 - (i - 1) * 38)
    local base = (i % 2 == 0) and C.row2 or C.row1
    row.base = base
    skin(row, base, C.clear)
    row.name = mkText(row, "GameFontHighlight", C.white)
    row.name:SetPoint("TOPLEFT", 12, -5)
    row.info = mkText(row, "GameFontHighlightSmall", C.muted)
    row.info:SetPoint("BOTTOMLEFT", 12, 5)
    row.info:SetWidth(380)
    row.info:SetWordWrap(false)
    row.btn = mkButton(row, "Remove", 64, 22, C.danger)
    row.btn:SetPoint("RIGHT", -8, 0)
    row.btn:SetScript("OnClick", function() removeEntry(row.key) end)
    row.locked = mkText(row, "GameFontHighlightSmall", { 0.5, 0.48, 0.7, 1 })
    row.locked:SetPoint("RIGHT", -12, 0)
    row.locked:SetText("owner only")
    row:SetScript("OnEnter", function(s)
      if s.SetBackdropColor then s:SetBackdropColor(C.rowHot[1], C.rowHot[2], C.rowHot[3], 1) end
      local e = s.entry
      if e then
        GameTooltip:SetOwner(s, "ANCHOR_RIGHT")
        GameTooltip:AddLine(e.name, 1, 1, 1)
        GameTooltip:AddLine("Added by: " .. e.owner, 0.6, 0.85, 1)
        GameTooltip:AddLine("Date: " .. date("%Y-%m-%d %H:%M", e.time), 0.8, 0.8, 0.9)
        if e.reason and e.reason ~= "" then GameTooltip:AddLine("Reason: " .. e.reason, 1, 0.85, 0.4, true) end
        GameTooltip:AddLine(" ")
        if e.owner == me then
          GameTooltip:AddLine("You added this player - you can remove them.", 0.4, 1, 0.5, true)
        else
          GameTooltip:AddLine("Only " .. e.owner .. " can remove this entry.", 1, 0.5, 0.5, true)
        end
        GameTooltip:Show()
      end
    end)
    row:SetScript("OnLeave", function(s)
      if s.SetBackdropColor then s:SetBackdropColor(s.base[1], s.base[2], s.base[3], 1) end
      GameTooltip:Hide()
    end)
    ui.rows[i] = row
  end

  ui.empty = mkText(p1, "GameFontHighlight", C.muted)
  ui.empty:SetPoint("TOP", 0, -150)
  ui.empty:SetJustifyH("CENTER")
  ui.empty:SetText("The blacklist is empty.\nTarget a player and press Add.")

  local prev = mkButton(p1, "<", 34, 24, C.btn)
  prev:SetPoint("BOTTOMLEFT", 0, 0)
  prev:SetScript("OnClick", function() page = page - 1; updateUI() end)
  local nxt = mkButton(p1, ">", 34, 24, C.btn)
  nxt:SetPoint("BOTTOMRIGHT", 0, 0)
  nxt:SetScript("OnClick", function() page = page + 1; updateUI() end)
  ui.pageText = mkText(p1, "GameFontHighlightSmall", C.muted)
  ui.pageText:SetJustifyH("CENTER")
  ui.pageText:SetPoint("BOTTOM", 0, 6)

  -- page 2: settings & sync --------------------------------------------------
  local p2 = CreateFrame("Frame", nil, ui)
  p2:SetPoint("TOPLEFT", 12, -98)
  p2:SetPoint("BOTTOMRIGHT", -12, 36)
  ui.pageSet = p2

  local h1 = mkText(p2, "GameFontNormal", C.gold)
  h1:SetPoint("TOPLEFT", 0, 0)
  h1:SetText("Behaviour")

  ui.tglIgnore = mkToggle(p2, "Auto-ignore blacklisted players",
    "Hides their whispers and declines their party invites.",
    function() return S.mode == "ignore" end,
    function(v) S.mode = v and "ignore" or "warn" end)
  ui.tglIgnore:SetPoint("TOPLEFT", 0, -20)

  ui.tglReply = mkToggle(p2, "Send an auto-reply",
    "Answers blacklisted players who whisper you (once per 10 minutes).",
    function() return S.autoreply end,
    function(v) S.autoreply = v and true or false end)
  ui.tglReply:SetPoint("TOPLEFT", 0, -56)

  ui.tglMinimap = mkToggle(p2, "Show minimap button",
    "Left-click: window  -  Right-click: warn / auto-ignore.",
    function() return not S.minimapHide end,
    function(v) S.minimapHide = not v; updateMinimap() end)
  ui.tglMinimap:SetPoint("TOPLEFT", 0, -92)

  ui.tglNotify = mkToggle(p2, "Chat messages about list changes",
    "Tell me in chat when another mage adds or removes a player.",
    function() return S.notify ~= false end,
    function(v) S.notify = v and true or false end)
  ui.tglNotify:SetPoint("TOPLEFT", 0, -128)

  local h2 = mkText(p2, "GameFontNormal", C.gold)
  h2:SetPoint("TOPLEFT", 0, -174)
  h2:SetText("Auto-reply message")
  local vars = mkText(p2, "GameFontHighlightSmall", C.muted)
  vars:SetPoint("LEFT", h2, "RIGHT", 10, 0)
  vars:SetText("variables: {player} {owner} {reason}")

  local replyBox = mkEdit(p2, 476, 26, "Auto-reply message", 220)
  replyBox:SetPoint("TOPLEFT", 0, -194)
  local function saveReply()
    local t = trim(replyBox:GetText())
    if t == "" then t = DEFAULT_REPLY end
    S.replytext = string.sub(t, 1, 220)
    replyBox:SetText(S.replytext)
    replyBox:SetCursorPosition(0)
    replyBox:ClearFocus()
    msg("Auto-reply message saved.")
  end
  replyBox:SetScript("OnEnterPressed", saveReply)
  ui.replyBox = replyBox
  local saveBtn = mkButton(p2, "Save", 70, 24, C.accentB, C.accent)
  saveBtn:SetPoint("TOPLEFT", 0, -226)
  saveBtn:SetScript("OnClick", saveReply)
  local defBtn = mkButton(p2, "Default", 70, 24, C.btn)
  defBtn:SetPoint("LEFT", saveBtn, "RIGHT", 6, 0)
  defBtn:SetScript("OnClick", function() replyBox:SetText(DEFAULT_REPLY); saveReply() end)

  local h3 = mkText(p2, "GameFontNormal", C.gold)
  h3:SetPoint("TOPLEFT", 0, -268)
  h3:SetText("Sync")
  ui.scopeLine = mkText(p2, "GameFontHighlightSmall", C.white)
  ui.scopeLine:SetPoint("TOPLEFT", 0, -290)
  ui.peerLine = mkText(p2, "GameFontHighlightSmall", C.white)
  ui.peerLine:SetPoint("TOPLEFT", 0, -306)
  ui.linkLine = mkText(p2, "GameFontHighlightSmall", C.white)
  ui.linkLine:SetPoint("TOPLEFT", 0, -322)
  ui.rxLine = mkText(p2, "GameFontHighlightSmall", C.white)
  ui.rxLine:SetPoint("TOPLEFT", 0, -338)
  ui.txLine = mkText(p2, "GameFontHighlightSmall", C.white)
  ui.txLine:SetPoint("TOPLEFT", 0, -354)

  local syncBtn = mkButton(p2, "Sync now", 110, 26, C.accentB, C.accent)
  syncBtn:SetPoint("TOPLEFT", 0, -380)
  syncBtn:SetScript("OnClick", function() SlashCmdList["MAGEBL"]("sync") end)
  local reconBtn = mkButton(p2, "Reconnect", 110, 26, C.btn)
  reconBtn:SetPoint("LEFT", syncBtn, "RIGHT", 6, 0)
  reconBtn:SetScript("OnClick", function() SlashCmdList["MAGEBL"]("reconnect") end)
  local printBtn = mkButton(p2, "Print list to chat", 130, 26, C.btn)
  printBtn:SetPoint("LEFT", reconBtn, "RIGHT", 6, 0)
  printBtn:SetScript("OnClick", function() SlashCmdList["MAGEBL"]("list") end)

  local h4 = mkText(p2, "GameFontNormal", C.gold)
  h4:SetPoint("TOPLEFT", 0, -422)
  h4:SetText("Link a mage directly")
  local h4b = mkText(p2, "GameFontHighlightSmall", C.muted)
  h4b:SetPoint("LEFT", h4, "RIGHT", 10, 0)
  h4b:SetText("works even when you are on different backend realms")
  local linkBox = mkEdit(p2, 300, 26, "Mage name (First Surname)", 40)
  linkBox:SetPoint("TOPLEFT", 0, -442)
  local function doLink()
    local n = trim(linkBox:GetText())
    if n ~= "" then SlashCmdList["MAGEBL"]("link " .. n) end
    linkBox:SetText(""); linkBox:ClearFocus()
  end
  linkBox:SetScript("OnEnterPressed", doLink)
  local linkBtn = mkButton(p2, "Link", 70, 26, C.accentB, C.accent)
  linkBtn:SetPoint("LEFT", linkBox, "RIGHT", 6, 0)
  linkBtn:SetScript("OnClick", doLink)
  local linksBtn = mkButton(p2, "Show links", 90, 26, C.btn)
  linksBtn:SetPoint("LEFT", linkBtn, "RIGHT", 6, 0)
  linksBtn:SetScript("OnClick", function() SlashCmdList["MAGEBL"]("links") end)

  ui:SetScript("OnShow", function(s)
    ui.replyBox:SetText(S.replytext or DEFAULT_REPLY)
    ui.replyBox:SetCursorPosition(0)
    updateUI()
  end)
  ui:SetScript("OnUpdate", function(s, el)
    s.acc = (s.acc or 0) + (el or 0)
    if s.acc >= 1 then s.acc = 0; refreshStatus() end
  end)
  ui:Hide()
  selectTab(1)
end

local function toggleUI()
  if not enabled then refuse() return end
  buildUI()
  if ui:IsShown() then ui:Hide() else ui:Show() end
end

---------------------------------------------------------------------------
-- Minimap button
---------------------------------------------------------------------------
local mb

local function posMinimap()
  local a = math.rad(S.minimapAngle or 215)
  local w = Minimap:GetWidth()
  if type(w) ~= "number" or w < 50 then w = 140 end
  local r = w / 2 + 5
  mb:ClearAllPoints()
  mb:SetPoint("CENTER", Minimap, "CENTER", math.cos(a) * r, math.sin(a) * r)
end

local function dragUpdate()
  local mx, my = Minimap:GetCenter()
  local px, py = GetCursorPosition()
  local scale = Minimap:GetEffectiveScale()
  px, py = px / scale, py / scale
  S.minimapAngle = math.deg(math.atan2(py - my, px - mx))
  posMinimap()
end

local function showMinimapTooltip(owner, anchor)
  GameTooltip:SetOwner(owner, anchor or "ANCHOR_LEFT")
  GameTooltip:AddLine("Mage Portal Blacklist", 0.4, 0.88, 1)
  local n = 0
  for _, e in pairs(DB) do if e.active then n = n + 1 end end
  GameTooltip:AddLine("Blacklisted players: " .. n, 1, 1, 1)
  local _, text = status()
  GameTooltip:AddLine(text, 1, 1, 1)
  GameTooltip:AddLine("Mode: " .. (S.mode == "ignore" and "auto-ignore" or "warn only"), 1, 1, 1)
  GameTooltip:AddLine(" ")
  GameTooltip:AddLine("Left-click: open window", 0.7, 0.7, 0.7)
  GameTooltip:AddLine("Shift-left-click: sync now", 0.7, 0.7, 0.7)
  GameTooltip:AddLine("Right-click: toggle warn / auto-ignore", 0.7, 0.7, 0.7)
  GameTooltip:AddLine("Drag: move button", 0.7, 0.7, 0.7)
  GameTooltip:Show()
end

local function onMinimapClick(button)
  if button == "RightButton" then
    S.mode = (S.mode == "ignore") and "warn" or "ignore"
    msg("Mode: " .. (S.mode == "ignore" and "auto-ignore blacklisted players" or "warn only"))
    updateUI()
  elseif IsShiftKeyDown() then
    SlashCmdList["MAGEBL"]("sync")
  else
    toggleUI()
  end
end

local function buildMinimapInner()
  if mb and mb.ready then return end
  if not mb then
    mb = CreateFrame("Button", "MageBlacklistMinimapButton", Minimap or UIParent)
  end
  mb:SetSize(31, 31)
  mb:SetFrameStrata("MEDIUM")
  mb:SetFrameLevel(8)
  if mb.SetFixedFrameStrata then mb:SetFixedFrameStrata(true) end
  if mb.SetFixedFrameLevel then mb:SetFixedFrameLevel(true) end
  mb:RegisterForClicks("LeftButtonUp", "RightButtonUp")
  mb:RegisterForDrag("LeftButton")
  mb:SetHighlightTexture(136477)                        -- UI-Minimap-ZoomButton-Highlight

  if not mb.bg then
    mb.bg = mb:CreateTexture(nil, "BACKGROUND")
    mb.bg:SetSize(20, 20)
    mb.bg:SetTexture(136467)                            -- UI-Minimap-Background
    mb.bg:SetPoint("TOPLEFT", 7, -5)
    mb.icon = mb:CreateTexture(nil, "ARTWORK")
    mb.icon:SetSize(18, 18)
    mb.icon:SetTexture(iconTexture())
    mb.icon:SetTexCoord(0.07, 0.93, 0.07, 0.93)
    mb.icon:SetPoint("TOPLEFT", 7, -6)
    mb.border = mb:CreateTexture(nil, "OVERLAY")
    mb.border:SetSize(53, 53)
    mb.border:SetTexture(136430)                        -- MiniMap-TrackingBorder
    mb.border:SetPoint("TOPLEFT")
  end

  -- status dot: if the round mask fails for any reason, a plain square dot is used
  if not mb.dot then
    local ok, dot = pcall(mkDot, mb, 8)
    if not ok or not dot then
      dot = mb:CreateTexture(nil, "OVERLAY")
      dot:SetSize(7, 7)
      dot:SetColorTexture(1, 1, 1, 1)
      function dot:SetState(st)
        local c = (st == "ok" and C.green) or ((st == "idle" or st == "wait") and C.orange) or C.red
        self:SetColorTexture(c[1], c[2], c[3], 1)
      end
    end
    dot:SetPoint("BOTTOMRIGHT", -3, 4)
    mb.dot = dot
  end

  mb:SetScript("OnDragStart", function(self) self:SetScript("OnUpdate", dragUpdate) end)
  mb:SetScript("OnDragStop", function(self) self:SetScript("OnUpdate", nil) end)
  mb:SetScript("OnClick", function(self, button) onMinimapClick(button) end)
  mb:SetScript("OnEnter", function(self) showMinimapTooltip(self, "ANCHOR_LEFT") end)
  mb:SetScript("OnLeave", function() GameTooltip:Hide() end)
  posMinimap()
  mb.ready = true
  mb:Hide()
end

-- never lets an error in the button code break the rest of the addon; the error is reported once
local function buildMinimap()
  if mb and mb.ready then return true end
  local ok, err = pcall(buildMinimapInner)
  if not ok then
    net.minimapError = tostring(err)
    if not net.minimapErrorShown then
      net.minimapErrorShown = true
      msg("|cffff8040Minimap button problem:|r " .. net.minimapError .. "  (the addon still works: use /mbl or the AddOn list menu)")
    end
  end
  return ok
end

updateMinimap = function()
  if not mb or not mb.ready then return end
  if enabled and not S.minimapHide then mb:Show() else mb:Hide() end
  if mb.dot and mb.dot.SetState then mb.dot:SetState((status())) end
end

-- AddOn Compartment (the "+" menu next to the minimap): second, independent way to open the window
function MageBlacklist_OnCompartmentClick(addonName, buttonName)
  onMinimapClick(buttonName)
end
function MageBlacklist_OnCompartmentEnter(addonName, menuButtonFrame)
  showMinimapTooltip(menuButtonFrame, "ANCHOR_LEFT")
end
function MageBlacklist_OnCompartmentLeave()
  GameTooltip:Hide()
end

---------------------------------------------------------------------------
-- Channel join / announce / heartbeat
---------------------------------------------------------------------------
local function hideChannel()
  for i = 1, (NUM_CHAT_WINDOWS or 10) do
    local cf = _G["ChatFrame" .. i]
    if cf then pcall(ChatFrame_RemoveChannel, cf, CHANNEL) end
  end
  hidden = true
end

local function pingLinks()
  if not S then return end
  local q = queryText()
  if S.links then
    for k, l in pairs(S.links) do
      if not reachableByChannel(k) then sendTo(l.name, q) end
    end
  end
  if IsInGuild and IsInGuild() then sendGuild(q) end   -- finds guild mates on other backend realms
end

local function announce()
  net.announced = true
  C_Timer.After(2,  sendQuery)
  C_Timer.After(12, function() dump(true) end)   -- upload my own records
  C_Timer.After(25, sendQuery)
end

local function channelsLoaded()
  -- joining before the client has its normal channels can steal channel slot #1
  return select("#", GetChannelList()) > 0
end

local ticker
local function startTicker()
  if ticker then return end
  ticker = C_Timer.NewTicker(2, function()
    if not enabled then return end
    if chanId() == 0 then
      net.announced = false
      local t = GetTime()
      if (t - net.enterTime > 12 or channelsLoaded()) and t - net.lastJoin > 6 then
        net.lastJoin = t
        JoinChannelByName(CHANNEL)
      end
      refreshStatus()
      return
    end
    if not hidden then hideChannel() end
    if not net.announced then announce() end
  end)
end

local function heartbeat()
  if enabled then
    if chanId() > 0 then sendQuery() end
    pingLinks()
  end
  local t = GetTime()
  for k, v in pairs(net.seen) do if t - v > 60 then net.seen[k] = nil end end
  C_Timer.After(HEARTBEAT + math.random() * 30, heartbeat)
end
C_Timer.After(HEARTBEAT, heartbeat)

local function refresh()
  local ok = eligible()
  if ok and not enabled then
    enabled = true
    hidden = false
    net.announced = false
    msg("Active. Type /mbl to open the window or /mbl help for commands.")
    C_Timer.After(4, startTicker)
    C_Timer.After(12, pingLinks)
  elseif (not ok) and enabled then
    enabled = false
    LeaveChannelByName(CHANNEL)
    msg("Addon disabled (you are not a Mage level " .. MIN_LEVEL .. "+).")
  elseif (not ok) and not warnedDisabled then
    warnedDisabled = true
    msg("Addon inactive - it only works for Mages level " .. MIN_LEVEL .. " and above.")
  end
  refreshStatus()
end

---------------------------------------------------------------------------
-- Events
---------------------------------------------------------------------------
f:RegisterEvent("ADDON_LOADED")
f:RegisterEvent("PLAYER_ENTERING_WORLD")
f:RegisterEvent("PLAYER_LEVEL_UP")
f:RegisterEvent("CHAT_MSG_ADDON")
f:RegisterEvent("CHAT_MSG_ADDON_LOGGED")
f:RegisterEvent("CHAT_MSG_CHANNEL")
f:RegisterEvent("CHAT_MSG_CHANNEL_NOTICE")
f:RegisterEvent("CHAT_MSG_WHISPER")
f:RegisterEvent("PARTY_INVITE_REQUEST")
f:RegisterEvent("PLAYER_TARGET_CHANGED")
f:RegisterEvent("UPDATE_MOUSEOVER_UNIT")

f:SetScript("OnEvent", function(self, event, ...)
  if event == "ADDON_LOADED" then
    if ... ~= ADDON then return end
    MageBlacklistDB = MageBlacklistDB or {}
    MageBlacklistDB.lists    = MageBlacklistDB.lists    or {}
    MageBlacklistDB.settings = MageBlacklistDB.settings or {}
    DB, S = {}, MageBlacklistDB.settings   -- DB is bound to realm + faction on PLAYER_ENTERING_WORLD
    S.mode = S.mode or "warn"
    if not S.replytext or S.replytext == OLD_DEFAULT_1 then S.replytext = DEFAULT_REPLY end
    if C_ChatInfo and C_ChatInfo.RegisterAddonMessagePrefix then
      net.prefixResult = C_ChatInfo.RegisterAddonMessagePrefix(PREFIX)
    elseif RegisterAddonMessagePrefix then
      net.prefixResult = RegisterAddonMessagePrefix(PREFIX)
    end
    math.randomseed(time())
    buildMinimap()

  elseif event == "PLAYER_ENTERING_WORLD" then
    if net.enterTime == 0 then net.enterTime = GetTime() end
    buildMinimap()                                       -- retry if it failed at load time
    if mb and mb.icon then mb.icon:SetTexture(iconTexture()) end
    if ui and ui.icon then ui.icon:SetTexture(iconTexture()) end
    local full = GetUnitName and GetUnitName("player", true)
    if not full or not string.find(full, " ", 1, true) then full = unitFull("player") or full or "" end
    me = normName(full)
    myShort = me

    -- ONE channel and ONE list for every mage (names are unique per region on Forever).
    -- The channel itself only connects mages on the same backend realm; /mbl link bridges the rest.
    local realm = (GetRealmName and GetRealmName()) or ""
    scopeText = (realm ~= "" and realm or "?")
    local lists = MageBlacklistDB.lists
    lists.ALL = lists.ALL or {}
    local all = lists.ALL
    for k, l in pairs(lists) do              -- merge lists of older versions (per realm/faction) into one
      if k ~= "ALL" then
        for ek, e in pairs(l) do
          e.owner, e.name = normName(e.owner), normName(e.name)
          if better(e, all[ek]) then all[ek] = e end
        end
        lists[k] = nil
      end
    end
    if MageBlacklistDB.entries then
      for ek, e in pairs(MageBlacklistDB.entries) do
        e.owner, e.name = normName(e.owner), normName(e.name)
        if better(e, all[ek]) then all[ek] = e end
      end
      MageBlacklistDB.entries = nil
    end
    for _, e in pairs(all) do
      e.owner, e.name = normName(e.owner), normName(e.name)
    end
    DB = all
    local t = now()
    for k, e in pairs(DB) do
      if (not e.active) and t - e.ver > PRUNE_AGE then DB[k] = nil end
    end
    if S.links then
      for k, l in pairs(S.links) do
        if (not l.manual) and t - (l.t or 0) > LINK_TTL then S.links[k] = nil end
      end
    end
    refresh()

  elseif event == "PLAYER_LEVEL_UP" then
    C_Timer.After(1.5, refresh)

  elseif not enabled then
    return

  elseif event == "CHAT_MSG_ADDON" or event == "CHAT_MSG_ADDON_LOGGED" then
    local prefix, text, dist, sender = ...
    if prefix ~= PREFIX then return end
    net.lastDist = tostring(dist)
    local via = "addon"                                  -- CHANNEL
    if dist == "WHISPER" then
      via = "whisper"
    elseif dist == "GUILD" or dist == "OFFICER" or dist == "PARTY" or dist == "RAID" or dist == "INSTANCE_CHAT" then
      via = "guild"
    end
    handle(text, sender, via)

  elseif event == "CHAT_MSG_CHANNEL" then
    local text, sender, _, chName, _, _, _, _, baseName = ...
    if secret(text) or not text then return end
    if string.sub(text, 1, #CHAT_TAG) ~= CHAT_TAG then return end
    local nm = (not secret(chName) and chName) or (not secret(baseName) and baseName) or ""
    if not string.find(string.lower(nm), string.lower(CHANNEL_BASE), 1, true) then return end
    handle(string.sub(text, #CHAT_TAG + 1), sender, "chat")

  elseif event == "CHAT_MSG_CHANNEL_NOTICE" then
    local _, _, _, chName = ...
    if not secret(chName) and chName and string.find(string.lower(chName), string.lower(CHANNEL_BASE), 1, true) then
      hidden = false   -- the client may re-add the channel to chat windows; hide it again
    end

  elseif event == "CHAT_MSG_WHISPER" then
    local text, author = ...
    onWhisper(text, author)

  elseif event == "PARTY_INVITE_REQUEST" then
    local inviter = ...
    local e = isBlack(inviter)
    if e then
      if S.mode == "ignore" then
        StaticPopup_Hide("PARTY_INVITE")
        DeclineGroup()
        msg("Declined party invite from " .. e.name .. " (blacklisted).")
      else
        alert(inviter, "is inviting you to a party")
      end
    end

  elseif event == "PLAYER_TARGET_CHANGED" then
    if UnitExists("target") and UnitIsPlayer("target") then alert(unitFull("target"), "your target") end

  elseif event == "UPDATE_MOUSEOVER_UNIT" then
    if UnitExists("mouseover") and UnitIsPlayer("mouseover") then alert(unitFull("mouseover"), "under your mouse") end
  end
end)

---------------------------------------------------------------------------
-- Slash commands
---------------------------------------------------------------------------
SLASH_MAGEBL1 = "/mbl"
SLASH_MAGEBL2 = "/mageblacklist"
SlashCmdList["MAGEBL"] = function(input)
  local cmd, rest = string.match(input or "", "^(%S*)%s*(.-)$")
  cmd = string.lower(cmd or "")
  rest = rest or ""

  if cmd == "" or cmd == "show" then toggleUI() return end
  if not enabled then refuse() return end

  if cmd == "add" then
    local n, r = string.match(rest, "^([^;]*);?(.*)$")
    addEntry(n or "", r or "")

  elseif cmd == "remove" or cmd == "del" or cmd == "paid" then
    removeEntry(rest)

  elseif cmd == "list" then
    local list = sortedList()
    for _, e in ipairs(list) do
      msg(e.name .. " - added by " .. e.owner .. ((e.reason and e.reason ~= "") and (" - " .. e.reason) or ""))
    end
    msg("Total blacklisted: " .. #list)

  elseif cmd == "check" then
    local e = isBlack(trim(rest))
    if e then msg(e.name .. " IS blacklisted (added by " .. e.owner .. ").")
    else msg("'" .. trim(rest) .. "' is not on the blacklist.") end

  elseif cmd == "mode" then
    rest = string.lower(trim(rest))
    if rest == "warn" or rest == "ignore" then
      S.mode = rest
      msg("Mode: " .. (rest == "ignore" and "auto-ignore whispers and party invites" or "warn only"))
      updateUI()
    else
      msg("Usage: /mbl mode warn  or  /mbl mode ignore")
    end

  elseif cmd == "reply" then
    rest = string.lower(trim(rest))
    if rest == "on" or rest == "off" then
      S.autoreply = (rest == "on")
      msg("Auto-reply: " .. (S.autoreply and "on" or "off"))
      updateUI()
    else
      msg("Usage: /mbl reply on|off  -  set text with /mbl replytext Your text")
    end

  elseif cmd == "replytext" then
    rest = trim(rest)
    if rest ~= "" then S.replytext = string.sub(rest, 1, 220); msg("Auto-reply message saved.")
    else msg("Current auto-reply: " .. (S.replytext or DEFAULT_REPLY)) end

  elseif cmd == "minimap" then
    if string.lower(trim(rest)) == "reset" then
      S.minimapHide, S.minimapAngle = false, 215
      if buildMinimap() and mb and mb.ready then posMinimap() end
      updateMinimap()
      updateUI()
      msg("Minimap button reset to its default position.")
    else
      S.minimapHide = not S.minimapHide
      buildMinimap()
      updateMinimap()
      updateUI()
      msg("Minimap button " .. (S.minimapHide and "hidden." or "shown.") .. "  (/mbl minimap reset puts it back to the default spot)")
    end

  elseif cmd == "notify" then
    rest = string.lower(trim(rest))
    if rest == "on" or rest == "off" then
      S.notify = (rest == "on")
      msg("Chat messages about list changes: " .. (S.notify and "on" or "off"))
      updateUI()
    else
      msg("Usage: /mbl notify on|off   (currently " .. ((S.notify ~= false) and "on" or "off") .. ")")
    end

  elseif cmd == "sync" then
    if GetTime() - lastManualSync < 20 then msg("Please wait a moment before syncing again.") return end
    lastManualSync = GetTime()
    sendQuery()
    dump(true)
    pingLinks()
    msg("Sync request sent.")

  elseif cmd == "link" then
    local n = normName(trim(rest))
    if n == "" then msg("Usage: /mbl link First Surname   (a mage who also runs this addon)") return end
    if sameChar(n, me) then msg("That is you.") return end
    local isNew = addLink(n, true)
    sendTo(n, queryText())
    msg((isNew and "Direct link created to " or "Direct link refreshed: ") .. n ..
        ". It works across backend realms; the other mage is linked back automatically once the message arrives.")
    updateUI()

  elseif cmd == "unlink" then
    local k = string.lower(normName(trim(rest)))
    if S.links and S.links[k] then
      msg("Link to " .. S.links[k].name .. " removed.")
      S.links[k] = nil
      updateUI()
    else
      msg("No link to '" .. trim(rest) .. "'.")
    end

  elseif cmd == "links" then
    local n = 0
    for k, l in pairs(S.links or {}) do
      n = n + 1
      local p = net.peers[k]
      msg("  " .. l.name .. (l.manual and " (manual)" or " (auto)") ..
          (reachableByChannel(k) and " - also in my channel" or "") ..
          (p and ("  - heard " .. ago(GetTime() - p.t)) or "  - not heard this session"))
    end
    msg("Direct links: " .. n .. "  (add one with /mbl link First Surname)")

  elseif cmd == "reconnect" then
    LeaveChannelByName(CHANNEL)
    hidden, net.announced, net.lastJoin = false, false, 0
    net.addonRx, net.chatRx = false, false
    pingLinks()
    msg("Reconnecting to the sync channel...")

  elseif cmd == "debug" then
    msg("Version " .. VERSION .. "  |  me: '" .. me .. "'  |  backend realm: " .. scopeText)
    msg("Channel: " .. CHANNEL .. "  (id " .. chanId() .. ")  |  prefix registered: " .. tostring(net.prefixResult))
    local nl = 0
    if S.links then for _ in pairs(S.links) do nl = nl + 1 end end
    msg("Minimap button: " .. (mb and ("ready=" .. tostring(mb.ready) .. " shown=" .. tostring(mb:IsShown())) or "not created") ..
        (net.minimapError and ("  ERROR: " .. net.minimapError) or ""))
    msg("Direct links: " .. nl .. "  |  direct queue: " .. (wt - wh + 1) .. "  |  last direct send result: " .. tostring(net.lastWResult))
    msg("Peers: " .. peerCount() .. "  |  addon msgs received: " .. tostring(net.addonRx) ..
        "  |  chat fallback received: " .. tostring(net.chatRx))
    msg("Sent: " .. net.tx .. "  Received: " .. net.rx .. "  Dropped: " .. net.dropped ..
        "  Queue: " .. (qt - qh + 1) .. "  Rejected removals: " .. net.rejected)
    msg("Last addon send result: " .. tostring(net.lastResult) .. "  |  last chat send: " .. tostring(net.lastChatResult) ..
        "  |  last dist: " .. net.lastDist)
    for _, p in pairs(net.peers) do
      msg("  peer: " .. p.name .. (p.ver and (" (v" .. p.ver .. ")") or "") .. "  - " .. ago(GetTime() - p.t))
    end

  else
    msg("Commands:")
    msg("/mbl - open the window")
    msg("/mbl add Name Surname ; reason - add a player")
    msg("/mbl remove Name Surname (or /mbl paid ...) - remove (only the mage who added the player)")
    msg("/mbl list | /mbl check Name | /mbl sync | /mbl reconnect | /mbl debug")
    msg("/mbl minimap (hide/show) | /mbl minimap reset | /mbl notify on|off - chat messages when mages add/remove players")
    msg("/mbl link Name Surname | /mbl unlink Name | /mbl links - direct link to a mage on another backend realm")
    msg("/mbl mode warn|ignore - warn only / auto-ignore")
    msg("/mbl reply on|off, /mbl replytext Text - auto-reply (variables: {player} {owner} {reason})")
  end
end
