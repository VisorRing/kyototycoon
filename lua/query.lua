-- -*- mode: Fundamental; tab-width: 4; -*-
local kt = __kyototycoon__
local db1, dbs, dbtype, attrtype, idx, dbname, keynames, serialdb, sid, sid_len, optable
if kt then
	db1 = kt.db
	dbs = {}				-- dbs[name]
	dbtype = {}				-- dbtype[db] = type
	attrtype = {}			-- attrtype[db][attr] = type
	idx = {}				-- idx[db][attr].{db,[cidx,...]}
	dbname = {}				-- dbname[db] -> name
	keynames = {}			-- keynames[db] -> keyname
	serialdb = nil
	sid = ""				-- ユニークキーのプレフィックス
	sid_len = string.len (sid)
	optable = nil
end
-- DEBUG = true
local xtmax = 8589934592
local kNUL = "\x00"
local kFF = "\xff"
-- type labels::
local kPunctuation = 0		-- 0: 記号
local kSymbol = 1				-- 1: シンボル
local kNumber = 2				-- 2: 数値
local kString = 3				-- 3: 文字列
local kInteger = 4			-- 4: 整数
local kCons = 8				-- 8: cons cell
local kBoolean = 9			-- 9: boolean
local kVector = 16			-- 16: vector
local kTable = 17				-- 17: table
local kConsumerFn = 20		-- 20: function chain
local kEVarPrefixCh = "-"		-- E変数のプレフィックス
local mType = "-~-\1"			-- Map, Vectorタイプのtableに入れる。
local kEVarPrefix = "-*-\1"		-- E変数のプレフィックス
local prognOutmap = "output"
local prognOutmapTable = "output-table"
local prognError = "ERROR"
local parentEnv = "_parent"
local nParamError = "wrong number of parameters"
local paramError = "bad parameter"
local typeError = "bad type"
local typeMismatchError = "type mismatch"
local noDBError = "database not found"
local fnError = "bad function"
local indexError = "no index"
local nIndexError = "too many number of the index values"
local ConsumerPushEnv, ConsumerStarter
-- TExp ----------------------------------------------
function texp (text)
	local texp_1, texp_2, texp_3, texp_5, texp_6
	function texp_1 (w, text)
		if w == "(" then
			return texp_2 (text)
		elseif w == "[" then
			return texp_5 (text)
		elseif w == "{" then
			return texp_6 (text)
		elseif w == "'" then
			return texp_3 (text)
		else
			return nil	-- error
		end
	end
	function texp_2 (text)	-- '('...
		local ans = {}
		local t, w
		local car, cdr
		if text then
			t, w, text = lex (text)
			if not t then
			elseif t == kPunctuation then
				if w == ")" then
					return {}, text		-- エラーではないがnil
				else
					ans.car, text = texp_1 (w, text)
				end
			elseif t == kSymbol then
				ans.car = {w, [mType] = t}
			else
				ans.car = w
			end
			car = ans
			while text do
				t, w, text = lex (text)
				if not t then
					-- error 閉じてない
				elseif t == kPunctuation then
					if w == "." then
						car.cdr, text = texp (text)
						t, w, text = lex (text)
						if t == kPunctuation and w == ")" then
						else
							-- error cdrの後が閉じてない
						end
						break
					elseif w == ")" then
						if nullp (ans) then
							return nil, text
						else
							return ans, text
						end
					else
						cdr = {}
						cdr.car, text = texp_1 (w, text)
						car.cdr = cdr
						car = cdr
					end
				elseif t == kSymbol then
					cdr = {}
					cdr.car = {w, [mType] = t}
					car.cdr = cdr
					car = cdr
				else
					cdr = {}
					cdr.car = w
					car.cdr = cdr
					car = cdr
				end
			end
		end
		if nullp (ans) then
			return nil, text
		else
			return ans, text
		end
	end
	function texp_3 (text)			-- '...
		local ans
		ans, text = texp (text)
		return {car = {"quote"; [mType] = kSymbol}; cdr = {car = ans}}, text
	end
	function texp_5 (text)			-- [...
		local ans = {[mType] = kVector}
		while text do
			local  t, w
			t, w, text = lex (text)
			if not t then
				return nil				-- error
			elseif t == kPunctuation then
				if w == "]" then
					return ans, text
				else
					w, text = texp_1 (w, text)
					table.insert (ans, safenil (w))
				end
			elseif t == kSymbol then
				table.insert (ans, {w, [mType] = t})
			else
				table.insert (ans, w)
			end
		end
	end
	function texp_6 (text)			-- {...
		local ans = {[mType] = kTable}
		while text do
			local  t, w
			t, w, text = lex (text)
			if not t then
				return nil				-- error
			elseif t == kPunctuation then
				if w == "}" then
					return ans, text
				elseif w == "," then
				else
					return nil		-- error
				end
			elseif t == kSymbol or t == kString then
				local t0, w0
				t0, w0, text = lex (text)
				if (t0 == kPunctuation or t0 == kSymbol) and w0 == "=>" then
				else
					return nil			-- error
				end
				local w2
				w2, text = texp (text)
				ans[w] = safenil (w2)
			else
				return nil				-- error
			end
		end
	end
	--
	local t, w
	t, w, text = lex (text)
	if not t then
		return nil			-- error
	elseif t == kPunctuation then
		return texp_1 (w, text)
	elseif t == kSymbol then
		return {w, [mType] = t}, text
	else
		return w, text
	end
end

function texplist (text)
	return texp ("("..text..")")
end

function lex (text)			--> (Type, Obj); Type = kNumber/kString/kBoolean/kSymbol/kPunctuation
	local i, s, e
	if not text then return nil end
	s, i = string.find (text, "^%s*")
	if string.len (text) - i > 0 then
		i = i + 1
		s, e = string.find (text, "^[+-]?[0-9]+%.?", i)
		if s then
			-- number
			local s2, e2 = string.find (text, "^[0-9]+", e + 1)
			if s2 then
				e = e2
			end
			s2, e2 = string.find (text, "^[eE][+-]?[0-9]+", e + 1)
			if s2 then
				e = e2
			end
			return kNumber, tonumber (string.sub (text, s, e)), string.sub (text, e + 1)
		else
			s, e = string.find (text, "^\"", i)
			if s then
				-- string
				local ans = ""
				s = s + 1
				while true do
					i, e = string.find (text, "[\\\"]", s)
					if i then
						if string.sub (text, i, i) == "\\" then
							if s < e then
								ans = ans .. string.sub (text, s, e - 1)
							end
							s = e + 1
							local c = string.sub (text, s, s)
							s = s + 1
							if c == "t" then
								ans = ans .. "\t"
							elseif c == "n" then
								ans = ans .. "\n"
							elseif c == "r" then
								ans = ans .. "\r"
							else
								ans = ans .. c
							end
						else
							return kString, ans .. string.sub (text, s, e - 1), string.sub (text, e + 1)
						end
					else
						return kString, ans .. string.sub (text, s), ""
					end
				end
			else
				s, e = string.find (text, "^[a-zA-Z_<>=!:#&%^%$%%%*%+%-%?%/][a-zA-Z_0-9_<>=!:#&%^%$%%%*%+%-%?%/%.]*", i)
				if s then
					-- symbol
					s = string.sub (text, s, e)
					text = string.sub (text, e + 1)
					if s == "true" then
						return kBoolean, true, text
					elseif s == "false" then
						return kBoolean, false, text
					else
						return kSymbol, s, text
					end
				else
					-- punctuation
					s = string.sub (text, i, i)
					if s == ';' then		-- comment
						s, e = string.find (text, "\n", i)
						if s then
							return lex (string.sub (text, e + 1))
						else
							return nil
						end
					else
						return kPunctuation, string.sub (text, i, i), string.sub (text, i + 1)
					end
				end
			end
		end
	else
		return nil		-- END
	end
end

function tdump (t)
	if type (t) == "table" then
		local ans = "{"
		local n = 0
		if t then
			local keys = {}
			for k, v in pairs (t) do
				table.insert (keys, {k, v})
			end
			table.sort (keys, function (a, b)
									a = a[1] b = b[1]
									if type (a) == "string" then
										if type (b) == "string" then
											return a < b
										else
											return false
										end
									else
										if type (b) == "string" then
											return true
										elseif type (a) ~= "table" and type (b) ~= "table" then
											return a < b
										else
											return false
										end
									end
								end)
			for i, v in ipairs (keys) do
				if n == 0 then
					ans = ans .. describe (v[1]) .. ":"
				else
					ans = ans .. ", " .. describe (v[1]) .. ":"
				end
				if v[1] == mType then
					ans = ans .. typename (v[2])
				elseif type (v[2]) == "table" then
					ans = ans .. tdump (v[2])
				else
					ans = ans .. describe (v[2])
				end
				n = n + 1
			end
		end
		return ans .. "}"
	else
		return describe (t)
	end
end

-- DEBUG
function envdump (e)
	local ans = "{"
	local n = 0
	local keys = {}
	for k, v in pairs (e) do
		table.insert (keys, tostring (k))
	end
	table.sort (keys)
	for i, k in ipairs (keys) do
		if n == 0 then
			ans = ans .. k .. ":" .. texpdump (e[k])
		else
			ans = ans .. ", " .. k .. ":" .. texpdump (e[k])
		end
		n = n + 1
	end
	return ans .. "}"
end

-- DEBUG
function tabledump (t)
	if type (t) == "table" then
		local ans = "{"
		local n = 0
		local keys = {}
		for k, v in pairs (t) do
			table.insert (keys, tostring (k))
		end
		table.sort (keys)
		for i, k in ipairs (keys) do
			if n == 0 then
				ans = ans .. k .. ":" .. tostring (t[k])
			else
				ans = ans .. ", " .. k .. ":" .. tostring (t[k])
			end
			n = n + 1
		end
		return ans .. "}"
	else
		return tostring (t)
	end
end

-- ERROR Message
function arraydump (t)
	if type (t) == "table" then
		local ans = "["
		for i, v in ipairs (t) do
			if i == 1 then
				ans = ans .. arraydump (v)
			else
				ans = ans .. " " .. arraydump (v)
			end
		end
		return ans .. "]"
	elseif type (t) == "string" then
--		return "\""..t.."\""
		return t
	else
		return tostring (t)
	end
end

function describe (v)
	local t = type (v)
	if t == "nil" then
		return "()"
	elseif t == "string" then
		v = string.gsub (tostring (v), "([\\\"])", "\\%1")
		v = string.gsub (v, "\n", "\\n")
		v = string.gsub (v, "\r", "\\r")
		v = string.gsub (v, "\t", "\\t")
		v = string.gsub (v, "%c", function (c) return string.format ("\\%.3o", string.byte (c)) end)		-- XXX
		return ("\"" .. v .. "\"")
	elseif t == "table" then
		t = v[mType]
		if t then
			return texpdump (v, t)
		else
			return texpdump (v, kCons)
		end
	else
		return tostring (v)
	end
end

function typename (t)
	if t == kSymbol then
		return "Symbol"
	elseif t == kNumber then
		return "Number"
	elseif t == kString then
		return "String"
	elseif t == kCons then
		return "Cons"
	elseif t == kBoolean then
		return "Boolean"
	elseif t == kVector then
		return "Vector"
	elseif t == kTable then
		return "Table"
	elseif t == kConsumerFn then
		return "ConsumerFn"
	else
		return "type("..tostring (t)..")"
	end
end

function ttype (e)
	local t = type (e)
	if t == "nil" then
		return kCons
	elseif t == "number" then
		return kNumber
	elseif t == "string" then
		return kString
	elseif t == "boolean" then
		return kBoolean
	elseif t == "table" then
		local t = e[mType]
		if t == nil then
			return kCons
		else
			return t
		end
	end
end

function nullp (obj)
	return obj == nil or (type (obj) == "table" and not next (obj))
end

function consp (e)
	return type (e) == "table" and not e[mType] and next (e)
end

function vectorp (e)
	return type (e) == "table" and e[mType] == kVector
end

function tablep (e)
	return type (e) == "table" and e[mType] == kTable
end

function symbolp (e)
	return type (e) == "table" and e[mType] == kSymbol
end

function stringp (e)
	return type (e) == "string"
end

function quotep (cons)
	local e = cons.car
	return type (e) == "table" and e[mType] == kSymbol and e[1] == "quote"
end

function lambdap (e)
	return consp (e) and symbolp (e.car) and e.car[1] == "lambda"
end

function consumerfnp (e)
	return type (e) == "table" and e[mType] == kConsumerFn
end

function texpdump (e)	-- => STRING
	-- mini lispとの関係でnilは ()で表記する。
	local function texpdump_1 (e)
		local ans
		ans = texpdump (e.car)
		e = e.cdr
		local t = type (e)
		if t == "nil" then
			return ans
		elseif t == "table" and not e[mType] then
			if quotep (e) then
				return "'" .. texpdump (e.cdr.car)
			else
				return ans .. " " .. texpdump_1 (e)
			end
		else
			return ans .. " . " .. texpdump (e)
		end
	end
	--
	local t = type (e)
	if t == "nil" then
		return "()"
	elseif t == "number" then
		return tostring (e)
	elseif t == "string" then
		return describe (e)
	elseif t == "boolean" then
		return tostring (e)
	elseif t == "table" then
		t = e[mType]
		if not t then		-- kCons
			if nullp (e) then
				return "()"
			elseif quotep (e) then
				return "'" .. texpdump (e.cdr.car)
			else
				return "(" .. texpdump_1 (e) .. ")"
			end
		elseif t == kSymbol then
			return e[1]
		elseif t == kVector then
			local ans = "["
			for i, v in ipairs (e) do
				if i > 1 then
					ans = ans .. " "
				end
				ans = ans .. texpdump (v)
			end
			return ans .. "]"
		elseif t == kTable then
			local ans = "{"
			local c = 0
			for k, v in pairs (e) do
				if string.sub (k, 1, 1) ~= kEVarPrefixCh then
					if c > 0 then
						ans = ans .. " "
					end
					ans = ans .. describe (k) .. " => " .. texpdump (v)
					c = c + 1
				end
			end
			return ans .. "}"
		elseif t == kConsumerFn then
			return tdump (e)
		else
			return "[unknown obj]"
		end
	else
		return "[unknown type:"..t.."]"
	end
end

function ctrldump (str)
	local ans = ''
	str = tostring (str)
	for i, v in ipairs ({string.byte (str, 1, string.len (str))}) do
		if v < 32 then
			ans = ans .. string.format ('\\x%.2x', v)
		else
			ans = ans .. string.format ('%c', v)
		end
	end
	return ans
end

function texpdump_short (e)
	local s = texpdump (e)
	if (string.len (s) > 88) then
		return string.sub (s, 0, 80) .. " ... " .. string.sub (s, -3)
	else
		return s
	end
end

function t_to_string (e)
	local t = type (e)
	if t == "nil" then
		return ""
	elseif t == "table" then
		if not next (e) then		-- nullp
			return ""
		elseif e[mType] == kSymbol then
			return e[1]
		else
			return texpdump (e)
		end
	else
		return tostring (e)
	end
end

function t_to_number (e)
	local t = type (e)
	if t == "number" then
		return e
	elseif t == "string" then
		e = tonumber (e)
		if e == nil then
			return 0
		else
			return e
		end
	else
		return 0
	end
end

function t_to_numstr (e)
	local t = type (e)
	if t == "nil" then
		return ""
	elseif t == "number" then
		return e
	elseif t == "table" then
		if not next (e) then		-- nullp
			return ""
		else
			return texpdump (e)
		end
	else
		return tostring (e)
	end
end

function t_to_array (e)
	local ans = {}
	if vectorp (e) then
		for i, v in ipairs (e) do
			ans[i] = t_to_numstr (v)
		end
	end
	return ans
end

function t_to_table_nilfree (e)
	local ans = {}
	if tablep (e) then
		for k, v in pairs (e) do
			if k ~= mType and not nullp (v) then
				ans[k] = t_to_numstr (v)
			end
		end
	end
	return ans
end

function output_texp (obj, vec, tbl)
	if vectorp (vec) then
		for i, v in ipairs (vec) do
			obj[i] = texpdump (v)
			vec[i] = nil				-- pairs内で更新できる
		end
	end
	if tablep (tbl) then
		for k, v in pairs (tbl) do
			if string.sub (k, 1, 1) ~= kEVarPrefixCh then
				obj[k] = texpdump (v)
			end
			tbl[k] = nil
		end
	end
end

function to_string_opt (obj)
	if nullp (obj) then
		return nil
	elseif type (obj) == "string" then
		return obj
	else
		return t_to_string (obj)
	end
end

function to_numstr_opt (obj)
	if nullp (obj) then
		return nil
	elseif type (obj) == "string" or type (obj) == "number" then
		return obj
	else
		return t_to_string (obj)
	end
end

function to_number_opt (obj)
	if type (obj) == "number" then
		return obj
	else
		return nil
	end
end

function safenil (obj)
	if obj == nil then
		return {}
	else
		return obj
	end
end

function vectorPut (vec, idx, val)
	idx = idx + 1				-- 0始まり
	while idx > #vec do
		table.insert (vec, {})
	end
	vec[idx] = safenil (val)
end

function stringJoin (tbl, ch)
	local  ans = ''
	for i, v in ipairs (tbl) do
		if i == 1 then
			ans = v
		else
			ans = ans .. ch .. v
		end
	end
	return ans
end

function stringJoinSub (tbl, ch, i, j)
	local  ans = ''
	for x = i, j do
		if x == i then
			ans = tbl[x]
		else
			ans = ans .. ch .. tbl[x]
		end
	end
	return ans
end

function basename (path)
	return tostring (string.match (tostring (path), "[^/]+$"))
end

------------------------------------------------------------
--DOC:=KyotoTycoon Query=
--DOC:
--DOC:==DB記述ファイル
--DOC:プライマリDBと同じディレクトリのconfig.mlという名前のファイルに記述する。
--DOC:
--DOC:$premode:1
--DOC: 設定記述ブロック = (''設定記述'' ...)
--DOC: 設定記述 = ''シリアルDB記述'' / ''DB記述'' / ''サフィックス記述''
--DOC: シリアルDB記述 = ('''serial''' ''ファイル名'')
--DOC: DB記述 = ('''db''' ''ファイル名'' ''DB名'' ''キー属性名'' ''キーの型'' ''属性リスト'' ''インデックス記述'' ...)
--DOC: 属性リスト = {''属性名'' => 型名 ...}
--DOC: 型名 = '''int''' / '''integer''' / '''real''' / '''number''' / '''text'''
--DOC: インデックス記述 = ('''index''' ''ファイル名'' ''属性名''...)
--DOC: サフィックス記述 = ('''suffix''' ''テキスト'')
--DOC: サフィックスパス記述 = ('''suffix-file''' ''ファイルパス'')
--DOC: コメント = ";" 任意のテキスト LF
--DOC:例
--DOC: ((suffix "./suffix.conf")
--DOC:  (serial "serial.kct")
--DOC:  (db "db01.kct" "hash" "hid" "text" {"dmid" => text "pagehash" => text "dmid" => int "asid" => text}
--DOC:   (index "ix01.kct" "dmid")
--DOC:   (index "ix02.kct" "pagehash")
--DOC:   (index "ix03.kct" "dmid" "asid"))
--DOC:  (serial "ix04.kct")
--DOC:  (db "db02.kct" "user" "uid" {"name" => text "date" => int}
--DOC:   (index "ix05.kct" "name")
--DOC:   (index "ix06.kct" "date"))
--DOC: )
--DOC:
--DOC:*シリアルDB記述は、シリアル番号を保持するDBの指定。
--DOC:*DB記述は、Key-Valueを保持するDBのニックネームを指定する。
--DOC:*インデックス記述は、DB記述のDBのインデックスを定義する。
--//--DOC:*属性名に「key」、「xt」を設定することはできない。
--DOC:*属性名に「xt」、「mt」を設定することはできない。
--DOC:*サフィックス行で、シリアル番号のサフィックスを設定する。リテラルを直接指定するにはダブルクォートで囲む。またはファイルにより指定する。改行文字は含まれない。
--DOC:*サフィックスに使用できる文字には制限がある。
--DOC:*サフィックス行を指定しない時、変数 __kyototycoon__.sid からサフィックスを生成する。
--DOC:*マルチマスター構成でレプリケーションする時、異なるサフィックスをシリアル番号に割り当てて、キーの重複を防ぐ。
--DOC:
--DOC:==ktserverアップデート
--DOC:*Lua拡張の変数 "'''__kyototycoon__'''" のフィールドに "'''sid'''"を追加。
--DOC:
function initConf ()
	local cdb, fd, confdata, vtype, op, e, a, file, obj, name, key, el, attr
	local op, name, key, attr, file, cdb, obj
	local dir = kt.regex (db1:path (), "[^/]*$", "")
	dbs[''] = db1
	idx[db1] = {}
	if kt.sid then
		sid = ":" .. tostring (kt.sid)
		sid_len = string.len (sid)
	end
	cdb = db1
	fd = io.open (dir .. "config.ml")
	if fd then
		confdata = fd:read ("*a")
		io.close (fd)
		confdata, vtype = texp (confdata)
	end
	while consp (confdata) do
		op = confdata.car
		confdata = confdata.cdr
		if consp (op) then
			a = op.car
			e = op.cdr
			if symbolp (a) then
				a = a[1]
				if a == "serial" then		-- (serial FILE)
					file = e.car
					if file and stringp (file) then
						obj = kt.dbs[file]
						if obj then
							serialdb = obj
						else	-- error
							kt.log ("error", texpdump (op) .. ": file not found.")
							return
						end
					else	-- error
						kt.log ("error", texpdump (op) .. ": bad type.")
						return
					end
				elseif a == "db" then		-- (db FILE NAME KEY [TYPE] {ATTR => TYPE ...} INDEX...)
					if not e then kt.log ("error", texpdump (op) .. ": " .. nParamError) end
					file = e.car
					e = e.cdr
					if not e then kt.log ("error", texpdump (op) .. ": " .. nParamError) end
					name = e.car
					e = e.cdr
					if not e then kt.log ("error", texpdump (op) .. ": " .. nParamError) end
					key = e.car
					e = e.cdr
					vtype = kString
					if e then
						attr = e.car
						e = e.cdr
						if type (attr) == "string" then
							vtype = attr
							if e then
								attr = e.car
								e = e.cdr
							else
								attr = nil
							end
							if vtype == "int" or vtype == "integer" then
								vtype = kNumber
							elseif vtype == "real" or vtype == "number" then
								vtype = kNumber
							else
								vtype = kString
							end
						end
					else
						attr = nil
					end
					if stringp (file) and stringp (name) and stringp (key) and (nullp (attr) or tablep (attr)) then
						local attrspecs = {}
						obj = kt.dbs[file]
						if obj then
							dbs[name] = obj
							dbtype[obj] = vtype
							idx[obj] = {}
							cdb = obj
							dbname[obj] = name
							keynames[obj] = key
						else
							kt.log ("error", texpdump (op) .. ": db file not found.")
							return
						end
						if attr then
							attrtype[cdb] = attrspecs
							for k, v in pairs (attr) do
								if k ~= mType then
									if stringp (k) and k ~= "" and v and symbolp (v) then
										vtype = v[1]
										if vtype == "int" or vtype == "integer" then
											attrspecs[k] = kNumber
										elseif vtype == "real" or vtype == "number" then
											attrspecs[k] = kNumber
										else
											attrspecs[k] = kString
										end
									else
										kt.log ("error", texpdump (attr) .. ": bad type.")
										return
									end
								end
							end
						end
						el = e
						while consp (el) do
							op = el.car
							el = el.cdr
							if consp (op) then
								a = op.car
								e = op.cdr
								if symbolp (a) then
									a = a[1]
									if a == "index" then		-- (index FILE ATTR...)
										file = e.car
										e = e.cdr
										obj = kt.dbs[file]
										if obj then
											local idxspec = {}	-- {db:DBOBJ, attrspecs:LIST}
											local specs = {}
											local attrs = {}
											idxspec.db = kt.dbs[file]
											idxspec.attrspecs = specs
											while consp (e) do
												attr = e.car
												e = e.cdr
												vtype = attrspecs[attr]
												if stringp (attr) and vtype then
													table.insert (specs, {attr, vtype})
													table.insert (attrs, attr)
												elseif attr == key then		-- キーを含むインデックス
													table.insert (specs, {attr, "text"})
													table.insert (attrs, attr)
												else
													kt.log ("error", texpdump (op) .. ": bad name.")
													return
												end
											end
											idx[cdb][stringJoin (attrs, '+')] = idxspec
										else
											kt.log ("error", texpdump (op) .. ": db file not found.")
											return
										end
									else
										kt.log ("error", texpdump (op) .. ": bad function.")
										return
									end
								else
									kt.log ("error", texpdump (op) .. ": syntax error.")
									return
								end
							else
								kt.log ("error", texpdump (op) .. ": syntax error.")
								return
							end
						end
					else
						kt.log ("error", texpdump (op) .. ": bad parameter.")
						return
					end
				elseif a == "suffix" then			-- suffixタグ
					name = e.car
					if name and stringp (name) then
						sid = string.match (name, "[a-zA-Z_0-9_<>=!:&%^%$%%%*%+%-%?%/%.]+")
						sid_len = string.len (sid)
					else
						kt.log ("error", texpdump (op) .. ": bad parameter.")
						return
					end
				elseif a == "suffix-file" then		-- suffix-fileタグ
					file = e.car
					if file and stringp (file) then
						local fd = io.open (file, "r")
						if fd then
							name = fd:read ()
							io.close (fd)
							sid = string.match (name, "[a-zA-Z_0-9_<>=!:&%^%$%%%*%+%-%?%/%.]+")
							sid_len = string.len (sid)
						end
					else
						kt.log ("error", texpdump (op) .. ": bad parameter.")
						return
					end
				else	-- error
					kt.log ("error", texpdump (op) .. ": bad function.")
					return
				end
			else	-- error
				kt.log ("error", texpdump (op) .. ": syntax error.")
				return
			end
		else	-- error
			kt.log ("error", texpdump (op) .. ": syntax error.")
			return
		end
	end
	if DEBUG then
		print ("serial: " .. basename (serialdb))
		print ("suffix: " .. sid)
		for k, v in pairs (dbs) do
			print ("id[" .. tostring (k) .. "]: \"" .. basename (v:path ()) .. "\"")
		end
		for k, v in pairs (dbname) do
			print ("dbname[\"" .. basename (k:path ()) .. "\"]: " .. tostring (v))
		end
		for k, v in pairs (keynames) do
			print ("keynames[\"" .. basename (k:path ()) .. "\"]: " .. tostring (v))
		end
		for k, v in pairs (attrtype) do
			print ("attrtype[\"" .. basename (k:path ()) .. "\"]: " .. tdump (v))
		end
		for k, v in pairs (idx) do
			for k2, v2 in pairs (v) do
				print ("idx[\"" .. basename (k:path ()) .. "\"][" .. tostring (k2) .. "]: " .. "{db:\"" .. basename (v2.db:path ()) .. "\", attrspecs:" .. arraydump (v2.attrspecs) .. "}")
			end
		end
	end
end

function splitWord (pat, str)
	local ans = {}
	local s, t, e
	s = 1
	while true do
		t, e = string.find (str, pat, s)
		if t then
			table.insert (ans, string.sub (str, s, t - 1))
			s = e + 1
		else
			table.insert (ans, string.sub (str, s))
			break
		end
	end
	return ans
end

--DOC:==拡張S式==
--DOC:*数値
--DOC:** 1, -5, 32e5
--DOC:*文字列
--DOC:** "abc", "", "This is a pen.\n"
--DOC:*シンボル
--DOC:** ASymbol, +, >=
--DOC:*リスト = S式のペア
--DOC:** (), (1), (1 (2 . 3))
--DOC:*ベクタ = S式の列
--DOC:** [1 2 3], [], [a (1 2) [X Y Z]]
--DOC:*テーブル = 文字列とS式のペアの連想配列
--DOC:**{"a" => 1 "b" => (1 2 3) "c" => [a b c]}
--DOC:
--DOC:*数値、文字列、ベクタ、テーブルを評価しても、もとのまま。
--DOC:*シンボルを評価すると、シンボルにバインドされた値が返る。
--DOC:*リストを評価すると、リストの第一要素のシンボルにバインドされた関数を実行する。
--DOC:
--DOC:==環境変数
--DOC:*環境は、キーと値のペアの集合。キーを環境変数と呼ぶ。
--DOC:*環境を値とすることができる。環境は、入れ子構造をとる。
--DOC:*拡張S式でファンクションを記述した時、シンボルを評価すると環境変数の値を取り出す。
--DOC:*環境変数をピリオドで連結して、入れ子になった環境にアクセスできる。
--DOC:*prognスクリプト関数内で実行されるファンクションは、環境にアクセスできる。
--DOC:*prognスクリプト関数は、_envパラメータで、環境変数の初期値を与えることができる。
--DOC:*prognスクリプト関数は、環境変数'''output'''、'''output-table'''にバインドされた環境を出力する。
--DOC:*DBにアクセスするファンクションは、storeパラメータで指定した環境変数にレコードを格納し、procパラメータで指定したconcurrentファンクションを実行する。
--DOC:**DBのレコードは、属性名を変数名とする入れ子になった環境として変数に格納される。
--DOC:
--DOC:==検索インデックス
--DOC:*レコードの値からインデックスのキーを生成する。
--DOC:*属性のタイプがintegerの時、符号修正した64ビット整数をBase64エンコードしたものをキーとする。
--DOC:*属性のタイプがrealの時、符号修正した倍精度浮動小数点数をBase64エンコードしたものをキーとする。
--DOC:*属性のタイプがtextの時、そのままのデータをキーとする。
--DOC:*インデックスする対象の属性がnilの時、インデックスレコードを生成しない。
--DOC:*インデックス構造
--DOC:$premode:1
--DOC: ''属性値1'' '''NUL''' ''属性値2'' '''NUL''' ... '''NUL''' ''レコードキー'' => ''レコードキー''
--DOC:
--DOC:
--DOC:

function checkBool (val)
	return val and not nullp (val)
end

function tfind (tbl, val)
	local k, v
	for k, v in pairs (tbl) do
		if v == val and type (k) == "string" then
			return k
		end
	end
	return nil
end

function tcopy (dst, src)
	if src then
		for k, v in pairs (src) do
			dst[k] = v
		end
	end
end

function tappend (dst, src)
	if src then
		for i, v in ipairs (src) do
			table.insert (dst, v)
		end
	end
end

function equal (a, b)
	local t = type (a)
	if t == "nil" then
		if nullp (b) then
			return true
		else
			return false
		end
	elseif t == "table" then
		if not next (a) and nullp (b) then
			return true
		elseif type (b) == "table" then
			t = a[mType]
			if t == b[mType] then
				if t == kVector then
					return equalVector (a, b)
				elseif t == kTable then
					return equalTable (a, b)
				elseif t == kSymbol then
					return a[1] == b[1]
				else
					return equalCons (a, b)
				end
			else
				return false
			end
		end
	else
		return a == b
	end
end

function equalCons (a, b)		-- 両パラメータ共にCons型
	return a.car == b.car and a.cdr == b.cdr
end

function equalVector (a, b)		-- 両パラメータともにVector型
	if #a ~= #b then
		return false
	end
	for i, v in ipairs (a) do
		if not equal (v, b[i]) then
			return false
		end
	end
	return true
end

function equalTable (a, b)		-- 両パラメータ共にTable型
	for k, v in pairs (a) do
		if not equal (v, b[k]) then
			return false
		end
	end
	for k, v in pairs (b) do
		if not nullp (v) and not a[k] then
			return false
		end
	end
	return true
end

function filterProcPushEnv (kwenv, cmd, env)
	if kwenv.proc then
		if not consumerfnp (kwenv.proc) then writeFnError (env, cmd, kwenv.proc, typeError) return true end
		kwenv.proc = ConsumerPushEnv.new (env, kwenv.store, kwenv.proc)
	end
	return false
end

function filterOffset (kwenv)
	if kwenv.offset then
		kwenv.offset = tonumber (kwenv.offset)
	end
end

function filterLimit (kwenv)
	if kwenv.once then
		kwenv.limit = nil
	else
		if nullp (kwenv.limit) then
			kwenv.limit = nil
		else
			kwenv.limit = tonumber (kwenv.limit)
		end
	end
	if not nullp (kwenv.next) then
		kwenv.next = t_to_string (kwenv.next)
		if kwenv.next == "" then
			kwenv.next = nil
		end
	else
		kwenv.next = nil
	end
end

function procOffset (kwenv, cmd)
	if kwenv.offset and kwenv.offset > 0 then
--		if DEBUG then print ("==> " .. t_to_string (cmd.car) .. ": offset") end
		if DEBUG then debugLog (t_to_string (cmd.car) .. ": offset") end
		kwenv.offset = kwenv.offset - 1
		return true
	end
	return false
end

function procLimit (kwenv, cmd, key, env)
	if kwenv.once then
		if DEBUG then debugLog (t_to_string (cmd.car) .. ": once") end
		return false
	end
	if kwenv.limit then
		if kwenv.limit <= 0 then
			if DEBUG then debugLog (t_to_string (cmd.car) .. ": limit") end
			if key and kwenv.next then
				bindSym (kwenv.next, key, env)
			end
			kwenv._procbreak = true
			return false
		end
		kwenv.limit = kwenv.limit - 1
	end
	return true
end

function procVal (rc, kwenv)
	if kwenv["true"] then
		return true
	elseif kwenv["false"] then
		return false
	else
		return rc
	end
end

-----------------------------------------------------------------
-- prognコマンドは、concurrentファンクションに対してnext1する。

-- local変数をセットしてconcurrentファンクションを呼び出すconcurrentファンクション
ConsumerPushEnv = {}
ConsumerPushEnv.new = function (env, var, proc)
	if var then var = to_string_opt (var) end
	if var == "" then var = nil end
	local o = {
		[mType] = kConsumerFn;
		name = "ConsumerPushEnv";
	}
	if var then
		o.next1 = function (self, val)
					return pushEnv ({[var] = safenil (val)}, env,
									function (env)
										return proc:next1 (val)
									end)
				end
		o.next = function (self, key, obj)
					return pushEnv ({[var] = safenil (obj)}, env,
									function (env)
										return proc:next (key, obj)
									end)
				end
	else
		o.next1 = function (self, val)
					return proc:next1 (val)
				end
		o.next = function (self, key, obj)
					return proc:next (key, obj)
				end
	end
	return o
end

ConsumerStarter = {}
ConsumerStarter.new = function (cmd, kwenv, fn)
	local o = {
		[mType] = kConsumerFn;
		name = "ConsumerStarter";
		next1 = function (self, val)
--					if DEBUG then print ("==> " .. cmd .. ".next1 (" .. texpdump (val) .. ")...") end
					local rc = fn (nil, val)
					return procVal (rc, kwenv)
				end;
		next = function (self, key, obj)
--					if DEBUG then print ("==> " .. cmd .. ".next (" .. texpdump (key) .. ", " .. texpdump (obj) .. ")...") end
--					if DEBUG then print ("==> " .. cmd .. ".next (" .. texpdump (key) .. ", ***)...") end
					local rc = fn (key, obj)
					return procVal (rc, kwenv)
				end;
	}
	return o
end

------------------------------------------------------------
-- eはkCons
function writeFnError (env, cmd, name, msg)
	local c = ""
	if cmd then
		if type (cmd) == "string" then
			c = c .. cmd .. ": "
		else
			c = c .. texpdump_short (cmd) .. ": "
		end
	end
	if name then
		if type (name) == "string" then
			c = c .. name .. ": "
		else
			c = c .. texpdump_short (name) .. ": "
		end
	end
	c = c .. tostring (msg)
	if DEBUG then kt.log ("error", c) end
	if env then
		bindSym (prognError, c, env)			-- XXX local変数の影響を受ける
	end
end

local LogIndent = 0
function debugLog (msg, indent)
	if indent and indent < 0 then LogIndent = LogIndent + indent end
	if msg then
		print ("==> " .. string.rep (" | ", LogIndent) .. msg)
	end
	if indent and indent > 0 then LogIndent = LogIndent + indent end
end

function debugLogExp (msg)
	print (">   " .. string.rep (" | ", LogIndent) .. msg)
end

function debugProcVal (rc, indent)
	print ("==> " .. string.rep (" | ", LogIndent) .. "proc-value := " .. texpdump (rc))
	if indent and indent < 0 then LogIndent = LogIndent + indent end
end

-- kwlistのキーの値がtrueの時、パラメータを評価する。falseの時、パラメータを評価せずそのまま返す。
function readParams (cmd, env, kwlist, kwparam)
	local e = cmd.cdr
	local ans = {}
	local cons = ans
	local a, s, f
	if kwparam == nil then
		kwparam = {}
	end
	while consp (e) do
		a = e.car
		e = e.cdr
		if symbolp (a) then
			s = string.sub (a[1], 1, 1)
			if s == ":" then
				s = string.sub (a[1], 2)
				if kwlist then
					f = kwlist[s]
					if f then				-- true
						kwparam[s] = evalExpr (e.car, env)
						e = e.cdr
						goto Lp1
					elseif f ~= nil then	-- false
						kwparam[s] = e.car
						e = e.cdr
						goto Lp1
					end
				end
				writeFnError (env, cmd, a[1], paramError)
				return ans.cdr, kwparam
			elseif s == "#" then
				s = string.sub (a[1], 2)
				if kwlist then
					f = kwlist[s]
					if f ~= nil then		-- true or false
						kwparam[s] = true
						goto Lp1
					end
				end
				writeFnError (env, cmd, a[1], paramError)
				return ans.cdr, kwparam
			end
		end
		cons.cdr = {car = a}
		cons = cons.cdr
		::Lp1::
	end
	return ans.cdr, kwparam
end

function expr_cons (cmd, env)
	-- (cons OBJ OBJ) -> OBJ
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans = {}
	ans.car = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then
		ans.cdr = evalExpr (e.car, env)
		e = e.cdr
	end
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return ans
end

function expr_nth (cmd, env)
	-- (nth NUM LIST) -> OBJ
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local n = t_to_number (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local obj = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	while n > 0 and consp (obj) do
		obj = obj.cdr
		n = n - 1
	end
	if consp (obj) then
		return obj.car
	else
		return nil
	end
end

function expr_list (cmd, env)
	-- (list OBJ ...) -> OBJ
	local e = cmd.cdr
	local ans = {}
	local c = ans
	local d
	while consp (e) do
		d = {}
		d.car = evalExpr (e.car, env)
		e = e.cdr
		c.cdr = d
		c = d
	end
	return ans.cdr
end

function expr_vector (cmd, env)
	-- (vector OBJ ...) -> VECTOR
	local e = cmd.cdr
	local ans = {[mType] = kVector}
	local a
	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		table.insert (ans, safenil (a))
	end
	return ans
end

function expr_table (cmd, env)
	-- (table CONS ...) -> TABLE
	local e = cmd.cdr
	local ans = {[mType] = kTable}
	local a, b
	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if consp (a) then
			ans[t_to_string (a.car)] = safenil (a.cdr)		-- nil対策
		end
	end
	return ans
end

function expr_to_string (cmd, env)
	-- (to-string EXPR) -> STRING
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local a = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return t_to_string (a)
end

function expr_to_number (cmd, env)
	-- (to-number EXPR) -> NUMBER
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local a = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return t_to_number (a)
end

function expr_quote (cmd, env)
	-- 'OBJ -> OBJ
	local e = cmd.cdr
	if consp (e) then
		return e.car
	else
		return nil
	end
end

function expr_read_texp (cmd, env)
	-- (read-sexp TEXT) -> OBJ
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local a = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if type (a) == "string" then
		return texp (a)
	elseif nullp (a) then
		return nil
	else
		writeFnError (env, cmd, a, typeError)
	end
	return nil
end

function expr_dump_to_texp (cmd, env)
	-- (dump-to-sexp OBJ) -> TEXT
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local a = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return texpdump (a)
end

function expr_nop (fn, cmd, env)
	-- (fn NUMBER ...)
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans, a
	ans = tonumber (evalExpr (e.car, env))
	e = e.cdr
	if nullp (ans) then return nil end
	while consp (e) do
		a = tonumber (evalExpr (e.car, env))
		e = e.cdr
		if nullp (a) then
			return nil
		end
		ans = fn (ans, a)
	end
	return ans
end

function expr_add (cmd, env)
	-- (+ NUMBER NUMBER ...) -> NUMBER
	return expr_nop (function (a, b) return a + b end, cmd, env)
end

function expr_minus (cmd, env)
	-- (- NUMBER NUMBER ...) -> NUMBER
	return expr_nop (function (a, b) return a - b end, cmd, env)
end

function expr_mult (cmd, env)
	-- (* NUMBER NUMBER ...) -> NUMBER
	return expr_nop (function (a, b) return a * b end, cmd, env)
end

function expr_div (cmd, env)
	-- (/ NUMBER NUMBER ...) -> NUMBER
	return expr_nop (function (a, b) return a / b end, cmd, env)
end

function expr_mod (cmd, env)
	-- (% NUMBER NUMBER) -> NUMBER
	return expr_nop (function (a, b) return a % b end, cmd, env)
end

function expr_ncmp (fn, cmd, env)
	-- (fn NUMBER NUMBER)
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans, a
	ans = tonumber (evalExpr (e.car, env))
	e = e.cdr
	if nullp (ans) then return nil end
	while consp (e) do
		a = tonumber (evalExpr (e.car, env))
		e = e.cdr
		if nullp (a) then
			return nil
		end
		if not fn (ans, a) then return false end
		ans = a
	end
	return true
end

function expr_nlt (cmd, env)
	-- (< NUMBER NUMBER ...) -> BOOL
	return expr_ncmp (function (a, b) return a < b end, cmd, env)
end

function expr_nle (cmd, env)
	-- (<= NUMBER NUMBER ...) -> BOOL
	return expr_ncmp (function (a, b) return a <= b end, cmd, env)
end

function expr_ngt (cmd, env)
	-- (> NUMBER NUMBER ...) -> BOOL
	return expr_ncmp (function (a, b) return a > b end, cmd, env)
end

function expr_nge (cmd, env)
	-- (>= NUMBER NUMBER ...) -> BOOL
	return expr_ncmp (function (a, b) return a >= b end, cmd, env)
end

function expr_nequal (cmd, env)
	-- (= NUMBER NUMBER ...) -> BOOL
	return expr_ncmp (function (a, b) return a == b end, cmd, env)
end

function expr_notnequal (cmd, env)
	-- (!= NUMBER NUMBER ...) -> BOOL
	local a = expr_nequal (cmd, env)
	return not a
end

function expr_cmp (fn, cmd, env)
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	local a
	while consp (e) do
		a = t_to_string (evalExpr (e.car, env))
		e = e.cdr
		if not fn (ans, a) then return false end
		ans = a
	end
	return true
end

function expr_lt (cmd, env)
	-- (lt STRING STRING ...) -> BOOL
	return expr_cmp (function (a, b) return a < b end, cmd, env)
end

function expr_le (cmd, env)
	-- (le STRING STRING ...) -> BOOL
	return expr_cmp (function (a, b) return a <= b end, cmd, env)
end

function expr_gt (cmd, env)
	-- (gt STRING STRING ...) -> BOOL
	return expr_cmp (function (a, b) return a > b end, cmd, env)
end

function expr_ge (cmd, env)
	-- (ge STRING STRING ...) -> BOOL
	return expr_cmp (function (a, b) return a >= b end, cmd, env)
end

function expr_streq (cmd, env)
	-- (eq STRING STRING ...) -> BOOL
	return expr_cmp (function (a, b) return a == b end, cmd, env)
end

function expr_notstreq (cmd, env)
	-- (neq STRING STRING ...) -> BOOL
	return not expr_streq (cmd, env)
end

function expr_eq (cmd, env)
	-- (== OBJ OBJ ...) -> BOOL
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans = evalExpr (e.car, env)
	e = e.cdr
	if nullp (ans) then ans = nil end
	local a
	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if nullp (a) then a = nil end
		if ans ~= a then return false end
	end

	return true
end

function expr_equal (cmd, env)
	-- (equal OBJ OBJ ...) -> BOOL
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans = evalExpr (e.car, env)
	e = e.cdr
	if nullp (ans) then ans = nil end
	local a
	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if nullp (a) then a = nil end
		if not equal (ans, a) then return false end
	end

	return true
end

function expr_neq (cmd, env)
	-- (!== OBJ OBJ ...) -> BOOL
	local a = expr_eq (cmd, env)
	return not a
end

function expr_notequal (cmd, env)
	-- (nequal OBJ OBJ ...) -> BOOL
	local a = expr_equal (cmd, env)
	return not a
end

function expr_and (cmd, env)
	-- (and BOOL BOOL ...) -> BOOL
	local e = cmd.cdr
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if not checkBool (a) then
			return false
		end
	end

	return true
end

function expr_or (cmd, env)
	-- (or BOOL BOOL ...) -> BOOL
	local e = cmd.cdr
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if checkBool (a) then
			return true
		end
	end

	return false
end

function expr_not (cmd, env)
	-- (not BOOL) -> BOOL
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local a = evalExpr (e.car, env)

	return not checkBool (a)
end

function expr_nullp (cmd, env)
	-- (nullp OBJ ...) -> BOOL
	local e = cmd.cdr
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if not nullp (a) then
			return false
		end
	end
	return true
end

function expr_not_nullp (cmd, env)
	-- (not-nullp OBJ ...) -> BOOL
	local e = cmd.cdr
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if nullp (a) then
			return false
		end
	end
	return true
end

function expr_emptyp (cmd, env)
	-- (emptyp OBJ ...) -> BOOL
	local e = cmd.cdr
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if not (nullp (a) or a == "") then
			return false
		end
	end
	return true
end

function expr_not_emptyp (cmd, env)
	-- (not-emptyp OBJ ...) -> BOOL
	local e = cmd.cdr
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if nullp (a) or a == "" then
			return false
		end
	end
	return true
end

function expr_concat (cmd, env)
	-- (concat STRING STRING ...) -> STRING
	local e = cmd.cdr
	local ans = ""
	local a

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		ans = ans .. t_to_string (a)
	end
	return ans
end

function expr_substr (cmd, env)
	-- (substr STRING START [LENGTH]) -> STRING
	local e = cmd.cdr
	local text, start, len

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	text = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	start = evalExpr (e.car, env)
	e = e.cdr	
	if consp (e) then
		len = evalExpr (e.car, env)
		e = e.cdr
	end
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if type (text) ~= "string" then writeFnError (env, cmd, text, typeError) return nil end
	if type (start) ~= "number" then writeFnError (env, cmd, start, typeError) return nil end
	if len then
		if type (len) ~= "number" then writeFnError (env, cmd, len, typeError) return nil end
		return string.sub (text, start + 1, start + len)
	else
		return string.sub (text, start + 1)
	end
end

function expr_strlen (cmd, env)
	-- (strlen STRING) -> NUMBER
	local e = cmd.cdr
	local text

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	text = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return string.len (text)
end

function expr_regexp_match (cmd, env)
	-- (regexp PATTERN STRING) -> BOOL
	local e = cmd.cdr
	local pat, text

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	pat = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	text = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return kt.regex (text, pat)
end

function expr_split_char (cmd, env)
	-- (split-char STRING CHAR) -> LIST_of_STRING
	local e = cmd.cdr
	local text, ch

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	text = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	ch = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	local  ans = {[mType] = kVector}
	if (string.len (ch) > 0) then
		while true do
			local a, b = string.find (text, ch, 1, true)
			if a then
				table.insert (ans, string.sub (text, 1, a - 1))
				text = string.sub (text, b + 1)
			else
				table.insert (ans, text)
				break
			end
		end
	else
		table.insert (ans, text)
	end
	return ans
end

function expr_append (cmd, env)
	-- (append LIST ... LIST) -> LIST
	local e = cmd.cdr
	local ans = {}
	local a
	local cons = ans

	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if not nullp (a) then
			while consp (a) do
				cons.cdr = {}
				cons = cons.cdr
				cons.car = a.car
				a = a.cdr
			end
			if not nullp (a) then
				cons.cdr = a
				break
			end
		end
	end
	return ans.cdr
end

function expr_reverse (cmd, env)
	-- (reverse LIST) -> LIST
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local a = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	local t = type (a)
	if t == "table" then
		if not a[mType] and next (a) then		-- consp
			local ans = {}
			while consp (a) do
				ans.car = a.car
				ans = {cdr = ans}
				a = a.cdr
			end
			if not nullp (a) then
				writeFnError (env, cmd, nil, typeError)
			end
			return ans.cdr
		elseif a[mType] == kVector then			-- vectorp
			local ans = {[mType] = kVector}
			for i = #a, 1, -1 do
				table.insert (ans, safenil (a[i]))
			end
			return ans
		else
			return a
		end
	elseif t == "string" then
		return string.reverse (a)
	else
		return a
	end
end

function expr_vector_get (cmd, env)
	-- (vector-get VECTOR INDEX) -> OBJ
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local idx = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end
	if type (idx) ~= "number" then writeFnError (env, cmd, idx, typeError) return nil end

	return vec[idx + 1]
end

function expr_vector_back (cmd, env)
	-- (vector-back VECTOR) -> OBJ
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	return vec[#vec]
end

function expr_vector_put (cmd, env)
	-- (vector-put VECTOR INDEX OBJ) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local idx = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local val = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end
	if type (idx) ~= "number" then writeFnError (env, cmd, idx, typeError) return nil end

	vectorPut (vec, idx, val)

	return val
end

function expr_vector_del (cmd, env)
	-- (vector-del VECTOR INDEX_FROM [INDEX_TO]) -> OBJ
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local idxfrom = evalExpr (e.car, env)
	e = e.cdr
	local idxto
	if consp (e) then
		idxto = evalExpr (e.car, env)
		e = e.cdr
	else
		idxto = idxfrom
	end
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end
	if type (idxfrom) ~= "number" then writeFnError (env, cmd, idxfrom, typeError) return nil end
	if type (idxto) ~= "number" then writeFnError (env, cmd, idxto, typeError) return nil end
	idxfrom = idxfrom + 1
	idxto = idxto + 1
	if idxfrom < 1 then idxfrom = 1 end
	local ans
	for i = idxfrom, idxto do
		ans = table.remove (vec, idxfrom)
	end

	return ans
end

function expr_vector_push (cmd, env)
	-- (vector-push VECTOR OBJ) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local val = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	if DEBUG then debugLog ("vector-push (" .. texpdump_short (vec) .. ", " .. texpdump (val) .. ")") end
	table.insert (vec, safenil (val))

	return val
end

function expr_vector_pop (cmd, env)
	-- (vector-pop VECTOR) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end
	if #vec == 0 then return nil end

	if DEBUG then debugLog ("vector-pop (" .. texpdump_short (vec) .. ")") end
	return table.remove (vec, #vec)
end

function expr_vector_size (cmd, env)
	-- (vector-size VECTOR) -> SIZE
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	return #vec
end

function expr_vector_append (cmd, env)
	-- (vector-append VECTOR VECTOR ...) -> VECTOR
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr

	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	local a
	while consp (e) do
		a = evalExpr (e.car, env)
		e = e.cdr
		if not vectorp (a) then writeFnError (env, cmd, a, typeError) return nil end
		for i, v in ipairs (a) do
			table.insert (vec, v)
		end
	end
	return vec
end

function expr_vector_reverse (cmd, env)
	-- (vector-reverse VECTOR) -> VECTOR
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	local ans = {[mType] = kVector}
	local n = #vec + 1
	for i, v in ipairs (vec) do
		ans[n - i] = v
	end
	return ans
end

function sort_str_asc (vec)
	table.sort (vec,
				function (a, b)
					return tostring (a) < tostring (b)
				end)
end

function sort_str_desc (vec)
	table.sort (vec,
				function (a, b)
					return tostring (a) > tostring (b)
				end)
end

function sort_tbl_str_asc (vec, col)
	table.sort (vec,
				function (a, b)
					for i, v in ipairs (col) do
						local a1 = a[v]
						local b1 = b[v]
						if a1 == b1 then
						else
							return tostring (a1) < tostring (b1)
						end
					end
					return false
				end)
end

function sort_tbl_str_desc (vec, col)
	table.sort (vec,
				function (a, b)
					for i, v in ipairs (col) do
						local a1 = a[v]
						local b1 = b[v]
						if a1 == b1 then
						else
							return tostring (a1) > tostring (b1)
						end
					end
					return false
				end)
end

function sort_num_asc (vec)
	table.sort (vec,
				function (a, b)
					local x = tonumber (a)
					local y = tonumber (b)
					if x and y then
						return x < y
					else
						return tostring (a) < tostring (b)
					end
				end)
end

function sort_num_desc (vec)
	table.sort (vec,
				function (a, b)
					local x = tonumber (a)
					local y = tonumber (b)
					if x and y then
						return x > y
					else
						return tostring (a) > tostring (b)
					end
				end)
end

function sort_tbl_num_asc (vec, col)
	table.sort (vec,
				function (a, b)
					for i, v in ipairs (col) do
						local a1 = a[v]
						local b1 = b[v]
						if a1 == b1 then
						else
							local x = tonumber (a1)
							local y = tonumber (b1)
							if x and y then
								return x < y
							else
								return tostring (a1) < tostring (b1)
							end
						end
					end
				end)
end

function sort_tbl_num_desc (vec, col)
	table.sort (vec,
				function (a, b)
					for i, v in ipairs (col) do
						local a1 = a[v]
						local b1 = b[v]
						if a1 == b1 then
						else
							local x = tonumber (a1)
							local y = tonumber (b1)
							if x and y then
								return x > y
							else
								return tostring (a1) > tostring (b1)
							end
						end
					end
				end)
end

function expr_vector_sort (cmd, env)
	-- (vector-sort VECTOR [#asc | #desc] [#num | #text] [:col COLUMN_VECTOR]) -> VECTOR
	local params, kwenv = readParams (cmd, env,
											{asc = true;
											 desc = true;
											 num = true;
											 text = true;
											 col = true;
											})
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (params.car, env)
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	local indexType
	local index = {}
	if nullp (kwenv.col) then
	elseif vectorp (kwenv.col) then
		indexType = kVector
		for i, v in ipairs (kwenv.col) do
			local t = type (v)
			if t == "number" then
				table.insert (index, v + 1)
			elseif t == "string" then
				table.insert (index, v)
				indexType = kTable
			elseif symbolp (v) then
				table.insert (index, v[1])
			end
		end
	else
		local t = type (kwenv.col)
		if t == "string" then
			table.insert (index, kwenv.col)
			indexType = kTable
		elseif t == "number" then
			table.insert (index, kwenv.col + 1)
			indexType = kVector
		elseif symbolp (kwenv.col) then
			table.insert (index, kwenv.col[1])
		end
	end

	if not indexType then
		if kwenv.asc or not kwenv.desc then
			if kwenv.text or not kwenv.num then
				sort_str_asc (vec)
			else
				sort_num_asc (vec)
			end
		else
			if kwenv.text or not kwenv.num then
				sort_str_desc (vec)
			else
				sort_num_desc (vec)
			end
		end
	elseif indexType == kVector then
		if kwenv.asc or not kwenv.desc then
			if kwenv.text or not kwenv.num then
				sort_tbl_str_asc (vec, index)
			else
				sort_tbl_num_asc (vec, index)
			end
		else
			if kwenv.text or not kwenv.num then
				sort_tbl_str_desc (vec, index)
			else
				sort_tbl_num_desc (vec, index)
			end
		end
	elseif indexType == kTable then
		if kwenv.asc or not kwenv.desc then
			if kwenv.text or not kwenv.num then
				sort_tbl_str_asc (vec, index)
			else
				sort_tbl_num_asc (vec, index)
			end
		else
			if kwenv.text or not kwenv.num then
				sort_tbl_str_desc (vec, index)
			else
				sort_tbl_num_desc (vec, index)
			end
		end
	end

	return vec
end

function expr_vector_to_list (cmd, env)
	-- (vector-to-list VECTOR) -> LIST
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	local ans = {}
	local c = ans
	for i, v in ipairs (vec) do
		c.cdr = {car = v}
		c = c.cdr
	end

	return ans.cdr
end

function expr_list_to_vector (cmd, env)
	-- (list-to-vector VECTOR) -> LIST
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local list = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (list) then return nil end
	if not consp (list) then writeFnError (env, cmd, list, typeError) return nil end

	local ans = {[mType] = kVector}
	while consp (list) do
		table.insert (ans, list.car)
		list = list.cdr
	end

	return ans
end

function expr_table_get (cmd, env)
	-- (table-get TABLE KEY) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local key = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (tbl) then return nil end
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end
	if type (key) ~= "string" then writeFnError (env, cmd, key, typeError) return nil end

	return tbl[key]
end

function expr_table_put (cmd, env)
	-- (table-put TABLE KEY OBJ) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local key = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local val = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (tbl) then return nil end
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end
	if type (key) ~= "string" then writeFnError (env, cmd, key, typeError) return nil end

	tbl[key] = safenil (val)		-- XXX nil対策

	return val
end

function expr_table_del (cmd, env)
	-- (table-del TABLE KEY) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local key = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (tbl) then return nil end
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end
	if type (key) ~= "string" then writeFnError (env, cmd, key, typeError) return nil end

	local val = tbl[key]
	tbl[key] = nil

	return val
end

function expr_table_append (cmd, env)
	-- (table-append TABLE1 TABLE2 ...) -> TABLE1
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end
	local tbl2
	while consp (e) do
		tbl2 = evalExpr (e.car, env)
		e = e.cdr
		if not nullp (tbl2) then
			if not tablep (tbl2) then writeFnError (env, cmd, tbl2, typeError) return nil end
			for key, val in pairs (tbl2) do
				if string.sub (key, 1, 1) ~= kEVarPrefixCh then
					tbl[key] = val
				end
			end
		end
	end

	return tbl
end

function expr_table_keys (cmd, env)
	-- (table-keys TABLE) -> VECTOR
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end

	local vec = {[mType] = kVector}
	for k, v in pairs (tbl) do
		if string.sub (k, 1, 1) ~= kEVarPrefixCh then
			table.insert (vec, k)
		end
	end
	return vec
end

function expr_table_to_list (cmd, env)
	-- (table-to-list TABLE) -> LIST
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (tbl) then return nil end
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end

	local ans = {}
	local c = ans
	for k, v in pairs (tbl) do
		if string.sub (k, 1, 1) ~= kEVarPrefixCh then
			c.cdr = {car = {car = k; cdr = v}}
			c = c.cdr
		end
	end

	return ans.cdr
end

function expr_list_to_table (cmd, env)
	-- (list-to-table TABLE) -> LIST
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local list = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (list) then return nil end
	if not consp (list) then writeFnError (env, cmd, list, typeError) return nil end

	local ans = {[mType] = kTable}
	local k, v
	while consp (list) do
		if consp (list.car) then
			k = list.car.car
			v = list.car.cdr
			ans[t_to_string (k)] = v
		end
		list = list.cdr
	end

	return ans
end

function expr_cond (cmd, env)
	-- (cond (BOOL FUNC ...) ...) -> LAST_VALUE
	local e = cmd.cdr
	local prog, ans

	while consp (e) do
		prog = e.car
		e = e.cdr
		if consp (prog) then
			if checkBool (evalExpr (prog.car, env)) then
				if DEBUG then debugLog (nil, 1) debugLog ("true") end
				prog = prog.cdr
				while consp (prog) do
					ans = evalExpr (prog.car, env)
					prog = prog.cdr
				end
				if DEBUG then debugLog (nil, -1) end
				return ans
			end
		else
			writeFnError (env, cmd, prog, typeError)
		end
	end
	return nil
end

function setvar_proc (name, val, env, bindfn)
	if consp (name) then
		if nullp (val) then
			local p = name
			while consp (p) do
				name = p.car
				p = p.cdr
				bindfn (t_to_string (name), {}, env)		-- safenil
			end
		elseif vectorp (val) then
			local p = name
			local i = 1
			while consp (p) do
				name = p.car
				p = p.cdr
				bindfn (t_to_string (name), safenil (val[i]), env)
				i = i + 1
			end
		elseif consp (val) then
			local p = name
			local q = val
			while consp (p) do
				name = p.car
				p = p.cdr
				bindfn (t_to_string (name), safenil (q.car), env)
				q = q.cdr
				if not consp (q) then
					q = {}
				end
			end
		else
			writeFnError (env, cmd, val, "array type required.")
		end
	elseif stringp (name) then
		bindfn (name, val, env)
	elseif symbolp (name) then
		bindfn (name[1], val, env)
	end
end

function expr_setvar (cmd, env)
	-- (setvar NAME VALUE ...) -> VALUE
	-- (setvar LIST [LIST | VECTOR] ...) -> VALUE
	local e = cmd.cdr
	local name, val

	while consp (e) do
		name = evalExpr (e.car, env)
		e = e.cdr
		if consp (e) then
			val = evalExpr (e.car, env)
			e = e.cdr
		else
			val = nil
		end
		setvar_proc (name, val, env, bindSym)
	end
	return val
end

function expr_getvar (cmd, env)
	-- (getvar NAME :parent INT) -> VALUE
	local params, kwenv = readParams (cmd, env,
											{parent = true;
											});
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local name = t_to_string (evalExpr (params.car, env))
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if kwenv.parent then
		local v = tonumber (kwenv.parent)
		if v > 0 and #env - v > 0 then
			local newenv = {}
			for i = 1, #env - v do
				table.insert (newenv, env[i])
			end
			return evalSym (name, newenv)
		end
	end
	return evalSym (name, env)
end

function expr_setevar (cmd, env)
	-- (setevar NAME VALUE ...) -> VALUE
	-- (setevar LIST [LIST | VECTOR] ...) -> VALUE
	local e = cmd.cdr
	local name, val

	while consp (e) do
		name = evalExpr (e.car, env)
		e = e.cdr
		if consp (e) then
			val = evalExpr (e.car, env)
			e = e.cdr
		else
			val = nil
		end
		setvar_proc (name, val, env, function (x, y, e) bindSym (x, y, e, true) end)
	end
	return val
end

function expr_getevar (cmd, env)
	-- (getevar NAME :parent INT) -> VALUE
	local params, kwenv = readParams (cmd, env,
											{parent = true;
											});
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local name = t_to_string (evalExpr (params.car, env))
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if kwenv.parent then
		local v = tonumber (kwenv.parent)
		if v > 0 and #env - v > 0 then
			local newenv = {}
			for i = 1, #env - v do
				table.insert (newenv, env[i])
			end
			return evalSym (name, newenv, true)
		end
	end
	return evalSym (name, env, true)
end

function expr_progn (cmd, env)
	-- (progn FUNC ...) -> LAST_VALUE
	local e = cmd.cdr
	local ans

	if DEBUG then debugLog ("progn begin", 1) end
	while consp (e) do
		ans = evalExpr (e.car, env)
		e = e.cdr
	end
	if DEBUG then debugLog ("progn end", -1) end
	return ans
end

function expr_lambda (cmd, env)
	-- (lambda (PARAMS ...) FUNC ...) -> LAMBDA
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	if not nullp (e.car) and not consp (e.car) then writeFnError (env, cmd, e.car, typeError) return nil end
	return cmd
end

function makeQuote (e)
	if symbolp (e) then
		local c = string.sub (e[1], 1, 1)
		if c == ":" or s == "#" then
			return e
		else
			return {car = {"quote"; [mType] = kSymbol}; cdr = {car = e}}
		end
	elseif consp (e) then
		return {car = {"quote"; [mType] = kSymbol}; cdr = {car = e}}
	else
		return e
	end
end

function expr_apply (cmd, env)
	-- (apply SYMBOL OBJ ... LIST) -> OBJ
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local ans = {}
	local cons = ans
	local a
	ans.car = evalExpr (e.car, env)
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	while true do
		a = evalExpr (e.car, env)
		e = e.cdr
		if consp (e) then
			cons.cdr = {}
			cons = cons.cdr
			cons.car = makeQuote (a)
		else
			while consp (a) do
				cons.cdr = {}
				cons = cons.cdr
				cons.car = makeQuote (a.car)
				a = a.cdr
			end
			break
		end
	end
	return evalFunc (ans, env)
end

function expr_vector_each (cmd, env)
	-- (vector-each VAR VECTOR EXPR ...) -> nil
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local var = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if not nullp (vec) and not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end
	if nullp (vec) then return nil end

	local prog = e
	local ans
	local localEnv = {}
	pushEnv (localEnv, env, function (env)
								if DEBUG then debugLog ("vector-each begin", 1) end
								for i, v in ipairs (vec) do
									if var ~= "" then
										localEnv[var] = safenil (v)
										if DEBUG then debugLog (nil, -1) debugLog ("vector-each [" .. var .. " := " .. texpdump (v) .. "]", 1) end
									end
									e = prog
									while consp (e) do
										ans = evalExpr (e.car, env)
										e = e.cdr
									end
								end
								if DEBUG then debugLog ("vector-each end", -1) end
							end)
	return ans
end

function expr_table_each (cmd, env)
	-- (table-each VAR_KEY VAR_VAL TABLE EXPR ...) -> nil
	local e = cmd.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local varkey = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local varval = t_to_string (evalExpr (e.car, env))
	e = e.cdr
	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if not nullp (tbl) and not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end
	if nullp (tbl) then return nil end

	local prog = e
	local ans
	local localEnv = {}
	pushEnv (localEnv, env, function (env)
								if DEBUG then debugLog ("table-each begin", 1) end
								for k, v in pairs (tbl) do
--									if k ~= mType and k ~= kEVarPrefix then
									if string.sub (k, 1, 1) ~= kEVarPrefixCh then
										if varkey ~= "" then localEnv[varkey] = k end
										if varval ~= "" then localEnv[varval] = safenil (v) end
										if DEBUG then debugLog (nil, -1) debugLog ("table-each [" .. tostring (varkey) .. " := " .. texpdump (k) .. "; " .. tostring (varval) .. " := " .. texpdump (v) .. "]", 1) end
										e = prog
										while consp (e) do
											ans = evalExpr (e.car, env)
											e = e.cdr
										end
									end
								end
								if DEBUG then debugLog ("table-each end", -1) end
							end)
	return ans
end

function expr_proc (cmd, env)
	-- (proc PROCESSOR ...) -> nil
	local e = cmd.cdr
	local proc
	local rc

	while consp (e) do
		if DEBUG then debugLog ("proc begin", 1) end
		proc = evalExpr (e.car, env)
		e = e.cdr
		if consumerfnp (proc) then
			rc = proc:next (nil, nil)
			if DEBUG then debugProcVal (rc) end
			if not rc then break end
		end
		if DEBUG then debugLog ("proc end", -1) end
	end

	-- PROCESSORを実行済みなので、戻り値にPROCESSORを出力しない
	return nil
end

function expr_vector_eval (cmd, env)
	-- (vector-eval VECTOR) -> VECTOR
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (vec) then return nil end
	if not vectorp (vec) then writeFnError (env, cmd, vec, typeError) return nil end

	return evalVector (vec, env)
end

function expr_table_eval (cmd, env)
	-- (table-eval TABLE) -> TABLE
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = evalExpr (e.car, env)
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if nullp (tbl) then return nil end
	if not tablep (tbl) then writeFnError (env, cmd, tbl, typeError) return nil end

	return evalTable (tbl, env)
end

function expr_sleep (cmd, env)
	-- (sleep SECOND) -> nil
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end
	local sec = tonumber (evalExpr (e.car, env))
	e = e.cdr
	if consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	if sec then
		kt.sleep (sec)
	end
	return nil
end

------------------------------------------------------------
function cexpr_output (cmd, env)
	-- (output EXPR_SELECTOR ... :store VAR #once :limit INT :next VAR #true #false)
	local params, kwenv
	kwenv = {store = prognOutmap}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local sel = {}
	while consp (params) do
		table.insert (sel, params.car)
		params = params.cdr
	end

	filterLimit (kwenv)
	kwenv.store = t_to_string (kwenv.store)

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function (key, val)
							if DEBUG then debugLog ("output", 1) end
							local rc = procLimit (kwenv, cmd, key, env)
							if kwenv._procbreak then
							else
								local e, name = refTSym (kwenv.store, env)
								if e and name then
									local storemap = e[name]
									if nullp (storemap) then
										storemap = {[mType] = kVector}
										e[name] = storemap
									elseif not vectorp (storemap) then
										writeFnError (env, cmd, storemap, "not vector.")
										if DEBUG then debugLog (nil, -1) end
										return procVal (rc, kwenv)
									end
									for i, v in ipairs (sel) do
										table.insert (storemap, safenil (evalVTF (v, env)))	-- ベクタの要素数をずらさない
									end
									if DEBUG then debugLog ("output (" .. describe (name) .. ", " .. texpdump_short (storemap[#storemap]) .. ")") end
								end
							end
							if DEBUG then debugLog (nil, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_output_table (cmd, env)
	-- (output-table EXPR_VAR EXPR_VALUE ... :store VAR #once :limit INTEGER] :next VAR #true #false)
	local params, kwenv
	kwenv = {store = prognOutmapTable}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vkey
	local kv = {}
	while consp (params) do
		vkey = params.car
		params = params.cdr
		if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
		table.insert (kv, {vkey, params.car})
		params = params.cdr
	end

	filterLimit (kwenv)
	kwenv.store = t_to_string (kwenv.store)

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function (key, val)
							if DEBUG then debugLog ("output-table", 1) end
							local rc = procLimit (kwenv, cmd, key, env)
							if kwenv._procbreak then
							else
								local e, name = refTSym (kwenv.store, env)
								if e and name then
									local storemap = e[name]
									if nullp (storemap) then
										storemap = {[mType] = kTable}
										e[name] = storemap
									elseif type (storemap) ~= "table" then
										writeFnError (env, cmd, storemap, "not table.")
										if DEBUG then debugLog (nil, -1) end
										return procVal (rc, kwenv)
									end
									for i, v in ipairs (kv) do
										local k = t_to_string (evalExpr (v[1], env))
										if string.sub (k, 1, 1) == kEVarPrefixCh then
											writeFnError (env, cmd, k, "bad name.")
										else
											if k ~= "" then
												storemap[k] = safenil (evalVTF (v[2], env))		-- nil値は要素を削除する仕様は、ローカル変数の定義を削除してしまう。
												if DEBUG then debugLog ("output-table (" .. describe (name) .. ", {" .. describe (k) .. " => " .. texpdump_short (storemap[k]) .. "})") end
											end
										end
									end
								end
							end
							if DEBUG then debugLog (nil, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_count (cmd, env)
	-- (count EXPR_VAR :every NUM :residue NUM :proc PROCESSOR [#true | #false])
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{every = true;
										 residue = true;
										 store = true;
										 proc = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local var = t_to_string (evalExpr (params.car, env))
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if kwenv.every then
		kwenv.every = tonumber (kwenv.every)
		if kwenv.residue then
			kwenv.residue = tonumber (kwenv.residue)
		else
			kwenv.residue = 1
		end
	end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function (key, val)
							local rc = true
							local e, name = refTSym (var, env)
							if e and name then
								local v = e[name]
								if nullp (v) then
									v = 0
								elseif type (v) ~= "number" then
									writeFnError (env, cmd, v, typeError)
									return procVal (rc, kwenv)
								end
								v = v + 1
								e[name] = v
								if DEBUG then debugLog ("count (" .. tostring (name) .. " := " .. tostring (v) .. ")") end
								if kwenv.proc then
									if not kwenv.every or v % kwenv.every == kwenv.residue then
										if DEBUG then debugLog (nil, 1) end
										rc = kwenv.proc:next (key, v)
										if DEBUG then debugProcVal (rc, -1) end
									end
								end
							end
							return procVal (rc, kwenv)
						end)
end

function op_cexpr_store (cmd, env, eflag)
	-- (store VAR EXPR_VALUE ... #once :limit NUM :next VAR #true #false)
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vkey
	local kv = {}
	while consp (params) do
		vkey = params.car
		params = params.cdr
		if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
		table.insert (kv, {vkey, params.car})
		params = params.cdr
	end

	filterLimit (kwenv)

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function (key, val)
							if DEBUG then debugLog (t_to_string (cmd.car), 1) end
							local rc = procLimit (kwenv, cmd, key, env)
							if kwenv._procbreak then
							else
								for i, v in ipairs (kv) do
									local vkey = t_to_string (evalExpr (v[1], env))
									bindSym (vkey, safenil (evalVTF (v[2], env)), env, eflag)		-- nilは要素を削除する仕様はローカル変数の定義を削除してしまう
								end
							end
							if DEBUG then debugLog (nil, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_store (cmd, env)
	-- (store VAR EXPR_VALUE ... #once :limit NUM :next VAR #true #false)
	return op_cexpr_store (cmd, env, false)
end

function cexpr_e_store (cmd, env)
	-- (e-store VAR EXPR_VALUE ... #once :limit NUM :next VAR #true #false)
	return op_cexpr_store (cmd, env, true)
end

function op_cexpr_undef (cmd, env, eflag)
	-- (undef VAR...)
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{},
									kwenv)
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function (key, val)
							if DEBUG then debugLog (t_to_string (cmd.car), 1) end
							local p = params
							while consp (p) do
								local key = t_to_string (evalExpr (p.car, env))
								bindSym (key, nil, env, eflag)		-- nilは要素を削除
								p = p.cdr
							end
							if DEBUG then debugLog (nil, -1) end
							return true
						end)
end

function cexpr_undef (cmd, env)
	-- (undef VAR...)
	return op_cexpr_undef (cmd, env, false)
end

function cexpr_e_undef (cmd, env)
	-- (e-undef VAR...)
	return op_cexpr_undef (cmd, env, true)
end

function cexpr_select (cmd, env)
	-- (select [EXPR_CONDITION] :proc PROCESSOR :false-proc PROCESSOR #once :limit INT :next VAR :offset INT #true #false)
	local cond, params, kwenv
	params, kwenv = readParams (cmd, env,
										{proc = true;
										 ["false-proc"] = true;
										 once = true;
										 limit = true;
										 next = true;
										 offset = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)
	if consp (params) then
		cond = params.car
		params = params.cdr
	else
		cond = 1
	end
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	filterOffset (kwenv)
	filterLimit (kwenv)
	if kwenv.proc and not consumerfnp (kwenv.proc) then writeFnError (env, cmd, kwenv.proc, typeError) return nil end
	if kwenv["false-proc"] and not consumerfnp (kwenv["false-proc"]) then writeFnError (env, cmd, kwenv.proc, typeError) return nil end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function (key, val)
							local rc = true
							if DEBUG then debugLog ("select", 1) end
							if checkBool (evalFunc (cond, env)) then
								if DEBUG then debugLog ("true") end
								if not procOffset (kwenv, cmd) then
									rc = procLimit (kwenv, cmd, key, env)
									if kwenv._procbreak then
									elseif kwenv.proc then
										local rc2 = kwenv.proc:next (key, val)
										rc = rc and rc2
										if DEBUG then debugProcVal (rc) end
									end
								end
							else
								if DEBUG then debugLog ("false") end
								if kwenv["false-proc"] then
									if not procOffset (kwenv, cmd) then
										rc = procLimit (kwenv, cmd, key, env)
										if kwenv._procbreak then
										else
											local rc2 = kwenv["false-proc"]:next (key, val)
											rc = rc and rc2
											if DEBUG then debugProcVal (rc) end
										end
									end
								end
							end
							if DEBUG then debugLog (nil, -1) end
							return procVal (rc, kwenv)
						end)
end

function evalExpr_db (c, env, cmd)
	local db = evalExpr (c, env)
	if type (db) ~= "string" then
		writeFnError (env, cmd, db, typeError)
		return nil
	end
	local pdb = pickdb (db)
	if not pdb then
		writeFnError (env, cmd, db, noDBError)
		return nil
	end
	return pdb
end

function cexpr_dbadd_op (op, cmd, env)
	-- (op DB EXPR_KEY EXPR_TABLE :unique VECTOR_KEY :xt SEC :store VAR :proc PROCESSOR #true #false)
	local db, key, val
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 proc = true;
										 xt = true;
										 unique = true;
--										 ["unique-replace"] = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	key = params.car
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	val = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if kwenv.unique and not vectorp (kwenv.unique) then writeFnError (env, cmd, kwenv.unique, typeError) return nil end
--	if kwenv["unique-replace"] then
--		if not vectorp (kwenv["unique-replace"]) then writeFnError (env, cmd, kwenv["unique-replace"], typeError) return nil end
--		kwenv.unique = kwenv["unique-replace"]
--		kwenv.uniquereplace = true
--	end
	kwenv.xt = to_number_opt (kwenv.xt)

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vkey = to_string_opt (evalFunc (key, env))
							local vval = evalVTF (val, env)
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": " .. describe (vkey), 1) end
							local st, rc = op (kwenv.proc, db, vkey, vval, kwenv.xt, kwenv.unique, env, cmd)
							if DEBUG then debugProcVal (rc, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_dbadd (cmd, env)
	-- (add DB EXPR_KEY EXPR_TABLE [:xt SEC] [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_dbadd_op (op_dbadd, cmd, env)
end

function cexpr_set (cmd, env)
	-- (set DB EXPR_KEY EXPR_TABLE [:xt SEC] [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_dbadd_op (op_dbset, cmd, env)
end

function cexpr_update (cmd, env)
	-- (update DB EXPR_KEY EXPR_TABLE [:xt SEC] [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_dbadd_op (op_dbupdate, cmd, env)
end

function cexpr_increment_op (op, cmd, env)
	-- (op DB EXPR_KEY EXPR_ATTR [EXPR_VAL] :xt SEC :store VAR :proc PROCESSOR #true #false)
	local db, key, attr, delta
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 proc = true;
										 xt = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	key = params.car
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attr = params.car
	params = params.cdr
	if consp (params) then 
		delta = params.car
		params = params.cdr
	end
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	kwenv.xt = to_number_opt (kwenv.xt)

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vkey = to_string_opt (evalFunc (key, env))
							local vattr = to_string_opt (evalFunc (attr, env))
							local vdelta = to_number_opt (evalFunc (delta, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": key=" .. describe (vkey) .. ", attr=" .. describe (vattr) .. ", delta=" .. describe (vdelta), 1) end
							local st, rc = op (kwenv.proc, db, vkey, vattr, vdelta, kwenv.xt)
							if DEBUG then debugProcVal (rc, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_increment (cmd, env)
	-- (increment DB EXPR_KEY EXPR_ATTR EXPR_VAL [:xt SEC] [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_increment_op (op_increment, cmd, env)
end

function cexpr_decrement (cmd, env)
	-- (decrement DB EXPR_KEY EXPR_ATTR EXPR_VAL [:xt SEC] [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_increment_op (op_decrement, cmd, env)
end

function cexpr_del (cmd, env)
	-- (del DB EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	local db, key
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 proc = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	key = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vkey = to_string_opt (evalFunc (key, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": key=" .. describe (vkey), 1) end
							local st, rc = op_dbdel (kwenv.proc, db, vkey, nil)
							if DEBUG then debugProcVal (rc, -1) end
							return rc
						end)
end

function cexpr_index_iterate_del (cmd, env)
	-- (index-iterate-del DB ATTR_VECTOR EXPR_VECTOR_VALUE [:store VAR] [:proc PROCESSOR] [#true | #false] [#once | :limit NUM])
	local db, attr, val
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 proc = true;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attr = evalExpr (params.car, env)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	val = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if stringp (attr) then
		attr = {attr; [mType] = kVector}
	elseif vectorp (attr) then
		local a = {[mType] = kVector}
		for i, v in ipairs (attr) do
			table.insert (a, t_to_string (v))
		end
		attr = a
	else
		writeFnError (env, cmd, attr, typeError)
	end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]" .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vval = evalVTF (val, env)
							if not vectorp (vval) then
								vval = {vval; [mType] = kVector}
							end
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": attr=" .. texpdump (attr) .. ", val=" .. texpdump (vval), 1) end
							local st, rc = op_index_iterate_del (kwenv.proc, db, attr, vval, cmd, env, kwenv)
							if DEBUG then debugProcVal (rc, -1) end
							return rc
						end)
end

function cexpr_key_get_op (op, cmd, env)
	-- (op DB EXPR_KEY [#once] [:store VAR] [:proc PROCESSOR] [#true | #false])
	local db, key
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 proc = true;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	key = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function (k, v)
							local vkey = to_string_opt (evalFunc (key, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": key=" .. describe (vkey), 1) end
							local rc = procLimit (kwenv, cmd, k, env)
							if kwenv._procbreak then
								if DEBUG then debugProcVal (rc, -1) end
								return procVal (rc, kwenv)
							end
							local st, rc2 = op (kwenv.proc, db, vkey)
							rc = rc and rc2
							if DEBUG then debugProcVal (rc, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_pickoff (cmd, env)
	-- (pickoff DB EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_key_get_op (op_pickoff, cmd, env)
end

function cexpr_key_get (cmd, env)
	-- (get DB EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_key_get_op (op_key_get, cmd, env)
end

function cexpr_key_iterate (cmd, env)
	-- (op DB [#desc] [:start EXPR_START] [#once | :limit NUM] [:proc PROCESSOR] [#true | #false])
	local op, db
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{desc = true;
										 proc = true;
										 start = false;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)
	if kwenv.desc then op = op_key_iterate_desc else op = op_key_iterate end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function (key, val)
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car), 1) end
							local vstart = to_string_opt (evalFunc (kwenv.start, env))
							local st, rc = op (kwenv.proc, db, vstart, cmd, env, kwenv)
							if DEBUG then debugProcVal (rc, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_index_get (cmd, env)
	-- (index-get DB ATTR EXPR_VALUE [:start EXPR_START] [:proc PROCESSOR] [#true | #false])
	local db, attr, attrval
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{proc = true;
										 start = false;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attr = evalExpr (params.car, env)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attrval = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if stringp (attr) then
		attr = {attr; [mType] = kVector}
	elseif vectorp (attr) then
		-- string vectorにする
		local a = {[mType] = kVector}
		for i, v in ipairs (attr) do
			table.insert (a, t_to_string (v))
		end
		attr = a
	else
		writeFnError (env, cmd, attr, typeError)
	end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]."..t_to_string (cmd.car),
						kwenv,
						function (key, val)
							local vval = evalVTF (attrval, env)
							if not vectorp (vval) then
								vval = {vval; [mType] = kVector}
							end
							local vstart = to_string_opt (evalFunc (kwenv.start, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": attr=" .. texpdump (attr) .. ", val=" .. texpdump (vval), 1) end
							local st, rc = op_index_get (kwenv.proc, db, attr, vval, vstart, cmd, env, kwenv)
							if DEBUG then debugProcVal (rc, -1) end
							return rc
						end)
end

function cexpr_index_iterate_op (op_asc, op_desc, cmd, env)
	-- (index-iterate DB ATTR EXPR_VALUE [#desc] [:start EXPR_START] [#once | :limit NUM] [:proc PROCESSOR] [#true | #false])
	local op, db, attr, attrval
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{desc = true;
										 proc = true;
										 start = false;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attr = evalExpr (params.car, env)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attrval = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if stringp (attr) then
		attr = {attr; [mType] = kVector}
	elseif vectorp (attr) then
		-- string vectorにする
		local a = {[mType] = kVector}
		for i, v in ipairs (attr) do
			table.insert (a, t_to_string (v))
		end
		attr = a
	else
		writeFnError (env, cmd, attr, typeError)
	end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)
	if kwenv.desc then op = op_desc else op = op_asc end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]."..t_to_string (cmd.car),
						kwenv,
						function (key, val)
							local vval = evalVTF (attrval, env)
							if not vectorp (vval) then
								vval = {vval; [mType] = kVector}
							end
							local vstart = to_string_opt (evalFunc (kwenv.start, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": attr=" .. texpdump (attr) .. ", val=" .. texpdump (vval), 1) end
							local st, rc = op (kwenv.proc, db, attr, vval, vstart, cmd, env, kwenv)
							if DEBUG then debugProcVal (rc, -1) end
							return rc
						end)
end

function cexpr_index_iterate (cmd, env)
	-- (index-iterate DB ATTR EXPR_VALUE [#desc] [:start EXPR_START] [#once | :limit NUM] [:proc PROCESSOR] [#true | #false])
	return cexpr_index_iterate_op (op_index_iterate, op_index_iterate_desc, cmd, env)
end

function cexpr_key_prefix (cmd, env)
	-- (key-prefix DB ATTR EXPR_VALUE [#desc] [:start EXPR_START] [#once | :limit NUM] [:proc PROCESSOR] [#true | #false])
	local op, db, val
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{desc = true;
										 proc = true;
										 start = false;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	val = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)
	if kwenv.desc then op = op_key_prefix_desc else op = op_key_prefix end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vstart = to_string_opt (evalFunc (kwenv.start, env))
							local vval = to_string_opt (evalFunc (val, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": ...", 1) end
							local st, rc = op (kwenv.proc, db, vval, vstart, cmd, env, kwenv)
							if DEBUG then debugProcVal (rc, -1) end
							return rc
						end)
end

function cexpr_index_prefix (cmd, env)
	-- (index-prefix DB ATTR EXPR_VALUE [#desc] [:start EXPR_START] [#once | :limit NUM] [:proc PROCESSOR] [#true | #false])
	return cexpr_index_iterate_op (op_index_prefix, op_index_prefix_desc, cmd, env)
end

function cexpr_key_range (cmd, env)
	-- (key-range DB EXPR_VALUE_A EXPR_VALUE_B [:start EXPR_START] [:store VAR] [:proc PROCESSOR] [#true | #false] [#once | :limit NUM])
	local op, db, vala, valb
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{desc = true;
										 proc = true;
										 start = false;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	vala = params.car
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	valb = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)
	if kwenv.desc then op = op_key_range_desc else op = op_key_range end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vvala = to_numstr_opt (evalFunc (vala, env))
							local vvalb = to_numstr_opt (evalFunc (valb, env))
							local vstart = to_string_opt (evalFunc (kwenv.start, env))
							if vstart then vvala = vstart end
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": vala=" .. texpdump (vvala) .. ", valb=" .. texpdump (vvalb), 1) end
							local rc, rf = op (kwenv.proc, db, vvala, vvalb, cmd, env, kwenv)
							if DEBUG then debugProcVal (rf, -1) end
							return rf
						end)
end

function cexpr_index_range (cmd, env)
	-- (index-range DB ATTR EXPR_VALUE_A EXPR_VALUE_B [#desc] [:start EXPR_START] [:proc PROCESSOR] [#true | #false])
	local op, db, attr, vala, valb
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{desc = true;
										 proc = true;
										 start = false;
										 once = true;
										 limit = true;
										 next = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attr = evalExpr (params.car, env)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	vala = params.car
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	valb = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if stringp (attr) then
		attr = {attr; [mType] = kVector}
	elseif vectorp (attr) then
		local a = {[mType] = kVector}
		for i, v in ipairs (attr) do
			table.insert (a, t_to_string (v))
		end
		attr = a
	else
		writeFnError (env, cmd, attr, typeError)
	end
	if filterProcPushEnv (kwenv, cmd, env) then return nil end
	filterLimit (kwenv)
	if kwenv.desc then op = op_index_range_desc else op = op_index_range end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vvala = evalVTF (vala, env)
							local vvalb = evalVTF (valb, env)
							if not vectorp (vvala) then
								vvala = {vvala; [mType] = kVector}
							end
							if not vectorp (vvalb) then
								vvalb = {vvalb; [mType] = kVector}
							end
							local vstart = to_string_opt (evalFunc (kwenv.start, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": attr=" .. texpdump (attr) .. ", vala=" .. texpdump (vvala) .. ", valb=" .. texpdump (vvalb), 1) end
							local rc, rf = op (kwenv.proc, db, attr, vvala, vvalb, vstart, cmd, env, kwenv)
							if DEBUG then debugProcVal (rf, -1) end
							return rf
						end)
end

function cexpr_newserial_op (op, cmd, env)
	-- (op EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	local key
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{store = true;
										 proc = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	key = params.car
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						"[" .. tostring (dbname[db]) .. "]." .. t_to_string (cmd.car),
						kwenv,
						function ()
							local vkey = to_string_opt (evalFunc (key, env))
							if DEBUG then debugLog ("[" .. tostring (dbname[db]) .. "]." .. texpdump (cmd.car) .. ": key=" .. describe (vkey), 1) end
							local rc, rf = op (kwenv.proc, vkey)
							if DEBUG then debugProcVal (rf, -1) end
							return rf
						end)
end

function cexpr_new_serial (cmd, env)
	-- (new-serial EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_newserial_op (op_newserial, cmd, env)
end

function cexpr_last_serial (cmd, env)
	-- (last-serial EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_newserial_op (op_lastserial, cmd, env)
end

function cexpr_reset_db_serial (cmd, env)
	-- (reset-db-serial DB)
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{},
										{})

	local db
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function ()
							local rc = true
							if DEBUG then debugLog ("reset-db-serial: " .. tostring (dbname[db]), 1) end
							db_serial_reset (db)
							if DEBUG then debugLog (nil, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_dump_serial (cmd, env)
	-- (dump-serial [EXPR_KEY | :db EXPR_DB] :store VAR :proc PROCESSOR #true #false)
	-- 自動発番のキーのSIDとserialdbのSIDがマッチしなければならない。
	local params, kwenv
	kwenv = {store = "_"}
	params, kwenv = readParams (cmd, env,
										{db = false;
										 ["no-db"] = true;
										 store = true;
										 proc = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	local key
	if consp (params) then
		key = params.car
		params = params.cdr
		if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	end

	if filterProcPushEnv (kwenv, cmd, env) then return nil end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function ()
							local vkey
							if kwenv.db then
								local db = evalExpr_db (kwenv.db, env, cmd)
								if db then
									vkey = db:path () .. sid
								else
									vkey = nil
								end
								if DEBUG then debugLog (texpdump (cmd.car) .. ": db=" .. tostring (dbname[db]), 1) end
							else
								vkey = evalExpr (key, env)
								if vkey then
									vkey = t_to_string (vkey)
								end
								if DEBUG then debugLog (texpdump (cmd.car) .. ": key=" .. tostring (vkey), 1) end
							end
							local rt, rc
							if vkey then
								rt, rc = op_serial_get (kwenv.proc, vkey)
							else
								rt, rc = op_serial_dump (kwenv.proc, kwenv["no-db"])
							end
							if DEBUG then debugProcVal (rc, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_restore_serial (cmd, env)
	-- (restore-serial EXPR_KEY EXPR_VAL) -> nil
	-- (restore-serial :db EXPR_DB EXPR_VAL) -> nil
	-- (restore-serial EXPR_TABLE) -> nil
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{db = false;
										},
										{})

	local key, val
	if consp (params) then
		key = params.car
		params = params.cdr
		if consp (params) then
			val = params.car
			params = params.cdr
			if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
		end
	end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function ()
							local vkey, vval
							if kwenv.db then
								local db = evalExpr_db (kwenv.db, env, cmd)
								if db then
									vkey = db:path () .. sid
								else
									vkey = nil
								end
								vval = evalExpr (key, env)	-- パラメータがずれる
								if DEBUG then debugLog (texpdump (cmd.car) .. ": db=" .. tostring (dbname[db]), 1) end
							elseif key then
								vkey = evalExpr (key, env)
								vval = evalExpr (val, env)
								if DEBUG then debugLog (texpdump (cmd.car) .. ": key=" .. tostring (vkey), 1) end
							else
								if DEBUG then debugLog (texpdump (cmd.car) .. ": key=" .. tostring (vkey), 1) end
							end
							local rc = true
							if type (vkey) == "string" then
								if nullp (vval) then
									op_restore_serial (vkey)
								else
									op_restore_serial (vkey, t_to_string (vval))
								end
							elseif tablep (vkey) then
								op_restore_serial_table (vkey)
							end
							if DEBUG then debugLog (nil, -1) end
							return procVal (rc, kwenv)
						end)
end

function cexpr_pushmsg (cmd, env)
	-- (pushmsg DB EXPR_KEY EXPR_TABLE [:xt SEC] [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_dbadd_op (op_pushmsg, cmd, env)
end

function cexpr_popmsg (cmd, env)
	-- (popmsg DB EXPR_KEY [:store VAR] [:proc PROCESSOR] [#true | #false])
	return cexpr_key_get_op (op_popmsg, cmd, env)
end

function cexpr_coneval (cmd, env)
	-- (coneval EXPR ...)
	local e = cmd.cdr

	if not consp (e) then writeFnError (env, cmd, nil, nParamError) return nil end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						{},
						function ()
							local p = e
							while consp (p) do
								local c = evalExpr (p.car, env)
								p = p.cdr
							end
							return true
						end)
end

function op_localvar (outmap, e, cmd, env, eflag)
	local function op_var (name, val)
		local c = t_to_string (name)
		if c ~= "" and not string.find (c, ".", 1, true) then
			if string.sub (c, 1, 1) ~= kEVarPrefixCh then
				if eflag then
					outmap[kEVarPrefix .. c] = val
				else
					outmap[c] = val
				end
			end
		else
			writeFnError (env, cmd, c, "bad name")
			return true
		end
		return false
	end

	if not e then
	elseif consp (e) then
		while consp (e) do
			c = e.car
			e = e.cdr
			if op_var (c, {}) then return true end
		end
	elseif vectorp (e) then
		for i, v in ipairs (e) do
			if op_var (v, {}) then return true end
		end
	elseif tablep (e) then
		for k, v in pairs (e) do
			if op_var (k, v) then return true end
		end
	else
		if op_var (e, {}) then return true end
	end
	return false
end

function debugLogLocalVar (vars, env)
	for k, v in pairs (vars) do
		if string.sub (k, 1, string.len (kEVarPrefix)) == kEVarPrefix then
			debugLog ("[*" .. string.sub (k, string.len (kEVarPrefix) + 1) .. " := " .. texpdump_short (env[k]) .. "]")
		else
			debugLog ("[" .. k .. " := " .. texpdump_short (env[k]) .. "]")
		end
	end
end

function cexpr_conproc (cmd, env)
	-- (conproc :var VARDEF :e-var VARDEF :break-if EXPR #break-if-limit PROCESSOR ...)
	-- VARDEF ::= VAR
	-- VARDEF ::= (VAR ...)
	-- VARDEF ::= [VAR ...]
	-- VARDEF ::= {VAR => VAL ...}
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{["var"] = true;
										 ["e-var"] = true;
										 ["break-if"] = false;
										 ["on-break"] = true;
										 ["break-if-limit"] = true;
										 ["true"] = true;
										 ["false"] = true;
										},
									kwenv)

	local proc
	local procs = {}
	while consp (params) do
		proc = evalExpr (params.car, env)
		params = params.cdr
		if consumerfnp (proc) then
			table.insert (procs, proc)
		end
	end
	local breakif = kwenv["break-if"]

	local onbreak
	if consumerfnp (kwenv["on-break"]) then
		onbreak = kwenv["on-break"]
	end
	if kwenv.var or kwenv["e-var"] then
		local vars = {}
		local dvar = kwenv.var
		if dvar then
			if op_localvar (vars, dvar, cmd, env) then return nil end
		end
		dvar = kwenv["e-var"]
		if dvar then
			if op_localvar (vars, dvar, cmd, env, true) then return nil end
		end
		-- ローカル変数あり
		return ConsumerStarter.new (
							t_to_string (cmd.car),
							kwenv,
							function (key, val)
								if DEBUG then debugLog ("conproc begin", 1) end
								local localenv = {}
								-- このPROCESSORが繰り返し呼ばれた時、ローカル変数を初期化しなければならない。
								for k, v in pairs (vars) do
									localenv[k] = safenil (evalExpr (v))
								end
								if DEBUG then debugLogLocalVar (vars, localenv) end
								return pushEnv (localenv, env,
											function (env)
												local rc = true
												if breakif and checkBool (evalFunc (breakif, env)) then
													if DEBUG then debugLog ("break") end
													if onbreak then
														if DEBUG then debugLog ("on-break") end
														onbreak:next (key, val)
													end
												else
													for i, v in ipairs (procs) do
														rc = v:next (key, val)
														if DEBUG then debugProcVal (rc) end
														-- on-breakのためにprocessorを実行した後にもチェックする
														if breakif and checkBool (evalFunc (breakif, env)) then
															if DEBUG then debugLog ("break") end
															if onbreak then
																if DEBUG then debugLog ("on-break") end
																onbreak:next (key, val)
															end
															break
														end
														if kwenv["break-if-limit"] and not rc then
															if onbreak then
																if DEBUG then debugLog ("on-break") end
																onbreak:next (key, val)
															end
															break
														end
													end
												end
												if DEBUG then debugLog ("conproc end", -1) end
												return not kwenv["break-if-limit"] or rc
											end
										)
							end)
	else
		-- ローカル変数なし
		return ConsumerStarter.new (
							t_to_string (cmd.car),
							kwenv,
							function (key, val)
								if DEBUG then debugLog ("conproc begin", 1) end
								local rc = true
								if breakif and checkBool (evalFunc (breakif, env)) then
									if DEBUG then debugLog ("break") end
									if onbreak then
										if DEBUG then debugLog ("on-break") end
										onbreak:next (key, val)
									end
								else
									for i, v in ipairs (procs) do
										rc = v:next (key, val)
										if DEBUG then debugProcVal (rc) end
										-- on-breakのためにprocessorを実行した後にもチェックする
										if breakif and checkBool (evalFunc (breakif, env)) then
											if DEBUG then debugLog ("break") end
											if onbreak then
												if DEBUG then debugLog ("on-break") end
												onbreak:next (key, val)
											end
											break
										end
										if kwenv["break-if-limit"] and not rc then
											if onbreak then
												if DEBUG then debugLog ("on-break") end
												onbreak:next (key, val)
											end
											break
										end
									end
								end
								if DEBUG then debugLog ("conproc end", -1) end
								return not kwenv["break-if-limit"] or rc
							end)
	end
end

function cexpr_local_var (cmd, env)
	-- (local-var VARDEF)
	-- VARDEF ::= VAR ...
	-- VARDEF ::= {VAR => VAL ...}
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{},
									kwenv)
	local vars = {}
	local e
	while consp (params) do
		e = evalExpr (params.car, env)
		params = params.cdr
		if op_localvar (vars, e, cmd, env) then return nil end
	end
	return ConsumerStarter.new (
						t_to_string (cmd.car),
						{},
						function ()
							for k, v in pairs (vars) do
								env[#env][k] = safenil (evalExpr (v))
							end
							if DEBUG then debugLogLocalVar (vars, env[#env]) end
							return true
						end)
end

function cexpr_local_e_var (cmd, env)
	-- (local-e-var SYMBOL...)
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{},
									kwenv)
	local vars = {}
	local e
	while consp (params) do
		e = evalExpr (params.car, env)
		params = params.cdr
		if op_localvar (vars, e, cmd, env, true) then return nil end
	end
	return ConsumerStarter.new (
						t_to_string (cmd.car),
						{},
						function ()
							for k, v in pairs (vars) do
								env[#env][k] = safenil (evalExpr (v))
							end
							if DEBUG then debugLogLocalVar (vars, env[#env]) end
							return true
						end)
end

function cexpr_conproc_vector_each (cmd, env)
	-- (conproc-vector-each VAR EXPR_VECTOR #break-if-limit PROCESSOR ...) -> PROCESSOR
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{["break-if-limit"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local var = t_to_string (evalExpr (params.car, env))
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local vec = params.car
	params = params.cdr
	-- ループを通してlimitをカウントするため、ループの外で評価する。
	local proc = {}
	local p
	while consp (params) do
		p = evalExpr (params.car, env)
		params = params.cdr
		if not nullp (p) then
			if not consumerfnp (p) then writeFnError (env, cmd, p, typeError) return nil end
			table.insert (proc, p)
		end
	end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function ()
							local localEnv = {}
							return pushEnv (localEnv, env,
											function (env)
												local rc = true
												if DEBUG then debugLog ("conproc-vector-each begin", 1) end
												local vec2 = evalExpr (vec, env)
												if nullp (vec2) and not vectorp (vec2) then
													if DEBUG then debugLog ("conproc-vector-each end", -1) end
													return rc
												end
												for i, v in ipairs (vec2) do
													if var ~= "" then
														localEnv[var] = safenil (v)
													end
													if DEBUG then debugLog ("vector-each [" .. tostring (var) .. " := " .. texpdump (v) .. "]", -1) debugLog (nil, 1) end
													for j, p in ipairs (proc) do
														rc = p:next (nil, v)
														-- limitで中断する
														if DEBUG then debugProcVal (rc) end
														if kwenv["break-if-limit"] and not rc then
															if DEBUG then debugLog ("break") debugLog ("conproc-vector-each end", -1) end
															return rc
														end
													end
												end
												if DEBUG then debugLog ("conproc-vector-each end", -1) end
												return true
											end)
						end)
end

function cexpr_conproc_table_each (cmd, env)
	-- (conproc-table-each VAR_KEY VAR_VAL EXPR_TABLE #break-if-limit PROCESSOR ...) -> PROCESSOR
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{["break-if-limit"] = true;
										},
									kwenv)

	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local varkey = t_to_string (evalExpr (params.car, env))
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local varval = t_to_string (evalExpr (params.car, env))
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	local tbl = params.car
	params = params.cdr
	local proc = {}
	local p
	while consp (params) do
		p = evalExpr (params.car, env)
		params = params.cdr
		if not nullp (p) then
			if not consumerfnp (p) then writeFnError (env, cmd, p, typeError) return nil end
			table.insert (proc, p)
		end
	end

	return ConsumerStarter.new (
						t_to_string (cmd.car),
						kwenv,
						function ()
							local localEnv = {}
							return pushEnv (localEnv, env,
											function (env)
												local rc = true
												if DEBUG then debugLog ("conproc-table-each begin", 1) end
												local tbl2 = evalExpr (tbl, env)
												if nullp (tbl2) or not tablep (tbl2) then return rc end
												for k, v in pairs (tbl2) do
													if string.sub (k, 1, 1) ~= kEVarPrefixCh then
														if varkey ~= "" then
															localEnv[varkey] = k
														end
														if varval ~= "" then
															localEnv[varval] = safenil (v)
														end
														if DEBUG then debugLog ("conproc-table-each [" .. tostring (varkey) .. " := " .. texpdump (k) .. "; " .. tostring (varval) .. " := " .. texpdump (v) .. "]", -1) debugLog (nil, 1) end
														for j, p in ipairs (proc) do
															rc = p:next (nil, v)
															-- limitで中断する
															if DEBUG then debugProcVal (rc) end
															if kwenv["break-if-limit"] and not rc then
																if DEBUG then debugLog ("break") debugLog ("conproc-table-each end", -1) end
																return rc
															end
														end
													end
												end
												if DEBUG then debugLog ("conproc-table-each end", -1) end
												return true
											end)
						end)
end

function expr_reindex (cmd, env)
	-- (reindex DB ATTR) -> nil
	local params, kwenv
	params, kwenv = readParams (cmd, env,
										{},
										{})

	local db, attr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	db = evalExpr_db (params.car, env, cmd)
	params = params.cdr
	if not consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end
	attr = evalExpr (params.car, env)
	params = params.cdr
	if consp (params) then writeFnError (env, cmd, nil, nParamError) return nil end

	if not db then return nil end
	if stringp (attr) then
		attr = {attr; [mType] = kVector}
	elseif vectorp (attr) then
		-- string vectorにする
		local a = {[mType] = kVector}
		for i, v in ipairs (attr) do
			table.insert (a, t_to_string (v))
		end
		attr = a
	else
		writeFnError (env, cmd, attr, typeError)
	end

	op_reindex (db, attr)

	return nil
end

function expr_schema (cmd, env)
	-- (schema) -> TABLE
	local ans
	local fn = {next1 = function (self, tbl)
					ans = tbl
				end}
	op_schema (fn)
	return ans
end

optable = {
--DOC:
--DOC:==prognスクリプト関数
--DOC:*いくつかのスクリプト関数は、レコードに対する検索の条件式を指定することができる。
--DOC:*検索レコードに対して条件式を評価する。
--DOC:*レコードの属性値は、属性名を変数としてアクセスできる。
--DOC:
--DOC:|table:w=100%|t:c:w=14%|t:w=40%|t:|
--DOC:|h:ファンクション|h:パラメータ|h:説明|
------
--DOC:| cons |('''cons''' ''OBJ'' ''OBJ'') -> ''OBJ''|パラメータをcar部、cdr部とするconsセルを返す。|
		["cons"] = expr_cons;
--DOC:| nth |('''nth''' ''NUM'' ''LIST'') -> ''OBJ''|''LIST''の''NUM''番目の要素を返す。|
		["nth"] = expr_nth;
--DOC:| list |('''list''' ''OBJ'' ''OBJ'' ...) -> ''OBJ''|パラメータを要素とするリストを生成する。|
		["list"] = expr_list;
--DOC:| vector |('''vector''' ''OBJ'' ...) -> ''VECTOR''|ベクタ型データを生成する。|
		["vector"] = expr_vector;
--DOC:| table |('''table''' ''CONS'' ...) -> ''TABLE''|テーブル型データを生成する。|
		["table"] = expr_table;
--DOC:| to-string | ('''to-string''' ''EXPR'') -> ''STRING''|文字列型に変換する。|
		["to-string"] = expr_to_string;
--DOC:| to-number | ('''to-number''' ''EXPR'') -> ''NUMBER''|数値型に変換する。|
		["to-number"] = expr_to_number;
--DOC:| quote |('''quote''' ''OBJ'') -> OBJ<br>'''<zwsp>'<zwsp>'''''OBJ'' -> OBJ|パラメータを評価せず返す。|
		["quote"] = expr_quote;
--DOC:| read-sexp<br>read-texp|('''read-sexp''' ''TEXT'') -> ''OBJ''<br>('''read-texp''' ''TEXT'') -> ''OBJ''|S式のテキストを読み込んでオブジェクトを生成する。|
		["read-sexp"] = expr_read_texp;
		["read-texp"] = expr_read_texp;
--DOC:| dump-to-sexp<br>dump-to-texp|('''dump-to-sexp''' ''OBJ'') -> ''TEXT''<br>('''dump-to-texp''' ''OBJ'') -> ''TEXT''|オブジェクトをS式に変換する。|
		["dump-to-sexp"] = expr_dump_to_texp;
		["dump-to-texp"] = expr_dump_to_texp;
------
--DOC:| vector-get | ('''vector-get''' ''VECTOR'' ''INDEX'') -> ''OBJ''|''VECTOR''の要素を取り出す。''INDEX''は、0始まり。|
		["vector-get"] = expr_vector_get;
--DOC:| vector-back | ('''vector-back''' ''VECTOR'') -> ''OBJ''|''VECTOR''の最後の要素を取り出す。|
		["vector-back"] = expr_vector_back;
--DOC:| vector-put | ('''vector-put''' ''VECTOR'' ''INDEX'' ''OBJ'') -> ''OBJ''|''VECTOR''の要素を変更する。''INDEX''は、0始まり。|
		["vector-put"] = expr_vector_put;
--DOC:| vector-del | ('''vector-del''' ''VECTOR'' ''INDEX_FROM'' [''INDEX_TO'']) -> ''OBJ''|''VECTOR''の要素を削除する。''INDEX''は、0始まり。|
		["vector-del"] = expr_vector_del;
--DOC:| vector-push | ('''vector-push''' ''VECTOR'' ''OBJ'') -> ''OBJ''|''VECTOR''の末尾に''OBJ''を追加する。|
		["vector-push"] = expr_vector_push;
--DOC:| vector-pop | ('''vector-pop''' ''VECTOR'') -> ''OBJ''|''VECTOR''の末尾のオブジェクトを取り出して返す。|
		["vector-pop"] = expr_vector_pop;
--DOC:| vector-size | ('''vector-size''' ''VECTOR'') -> ''INTEGER''|''VECTOR''の要素数。|
		["vector-size"] = expr_vector_size;
--DOC:| vector-append | ('''vector-append''' ''VECTOR1'' ''VECTOR2'' ...) -> ''VECTOR1''|''VECTOR1''に2番目以降の''VECTOR''の要素を追加する。|
		["vector-append"] = expr_vector_append;
--DOC:| vector-reverse | ('''vector-reverse''' ''VECTOR'') -> ''VECTOR''|''VECTOR''の要素を逆順にしたベクタを返す。|
		["vector-reverse"] = expr_vector_reverse;
--DOC:| vector-sort | ('''vector-sort''' ''VECTOR'' [#asc &|; #desc] [#num &|; #text] [:col ''COLUM_VECTOR'']) -> ''VECTOR''|変数''VAR''に格納されたベクタの要素をソートして並べ替える。パラメータのベクタは書き換えられる。|
		["vector-sort"] = expr_vector_sort;
--DOC:| vector-to-list | ('''vector-to-list''' ''VECTOR'') -> ''LIST'' | ''VECTOR''の要素を持つリストを返す。|
		["vector-to-list"] = expr_vector_to_list;
--DOC:| list-to-vector | ('''list-to-vector''' ''LIST'') -> ''VECTOR'' | ''LIST''の要素を持つベクタを返す。|
		["list-to-vector"] = expr_list_to_vector;
--DOC:| table-get | ('''table-get''' ''TABLE'' ''KEY'') -> ''OBJ''|テーブルの要素を取り出す。|
		["table-get"] = expr_table_get;
--DOC:| table-put | ('''table-put''' ''TABLE'' ''KEY'' ''OBJ'') -> ''OBJ''|テーブルの要素を変更する。|
		["table-put"] = expr_table_put;
--DOC:| table-del | ('''table-del''' ''TABLE'' ''KEY'') -> ''OBJ''|テーブルの要素を削除する。|
		["table-del"] = expr_table_del;
--DOC:| table-append | ('''table-append''' ''TABLE1'' ''TABLE2'' ...) -> ''TABLE1''|テーブルTABLE2以降のテーブルの要素をTABLE1に追加する。|
		["table-append"] = expr_table_append;
--DOC:| table-keys | ('''table-keys''' ''TABLE'') -> ''VECTOR''|テーブル''TABLE''のキー要素を集めたベクタを返す。|
		["table-keys"] = expr_table_keys;
--DOC:| table-to-list | ('''table-to-list''' ''TABLE'') -> ''LIST'' | ''TABLE''の要素を持つリストを返す。|
		["table-to-list"] = expr_table_to_list;
--DOC:| list-to-table | ('''list-to-table''' ''LIST'') -> ''TABLE'' | ''LIST''の要素を持つテーブルを返す。|
		["list-to-table"] = expr_list_to_table;
------
--DOC:| + |('''+''' ''NUMBER'' ''NUMBER'' ...) -> ''NUMBER''|数値の加算。パラメータを全て加算する。|
-- --DOC:|^|('''+''' ''STRING'' ''STRING'' ...) -> ''STRING''|文字列の連結。パラメータを全て連結する。|
		["+"] = expr_add;
--DOC:| - |('''-''' ''NUMBER'' ''NUMBER'' ...) -> ''NUMBER''|数値の減算。1番目のパラメータから、2番目以降の数値を減算する。|
		["-"] = expr_minus;
--DOC:| * |('''*''' ''NUMBER'' ''NUMBER'' ...) -> ''NUMBER''|数値の乗算。パラメータを全て乗算する。|
		["*"] = expr_mult;
--DOC:| / |('''/''' ''NUMBER'' ''NUMBER'' ...) -> ''NUMBER''|数値の除算。1番目のパラメータから、2番目以降の数値を除算する。|
		["/"] = expr_div;
--DOC:| % |('''%''' ''NUMBER'' ''NUMBER'') -> ''NUMBER''|数値の剰余。1番目のパラメータを2番目のパラメータで割った剰余を返す。|
		["%"] = expr_mod;
------
--DOC:| concat |('''concat''' ''STRING''...) -> ''STRING''|パラメータの文字列を連結した文字列を返す。|
		["concat"] = expr_concat;
--DOC:| substr |('''substr''' ''STRING'' ''START'' [''LENGTH'']) -> ''STRING''|文字列の切り出し。''START''は0はじまり。''LENGTH''を省略すると、末尾まで。|
		["substr"] = expr_substr;
--DOC:| strlen |('''strlen''' ''STRING'') -> ''NUMBER''|文字列の長さ。|
		["strlen"] = expr_strlen;
--DOC:| regexp-match |('''regexp-match''' ''PATTERN'' ''TEXT'') -> ''BOOL''|正規表現''PATTERN''に''TEXT''がマッチしたらtrueを返す。|
		["regexp-match"] = expr_regexp_match;
--DOC:| split-char |('''split-char''' ''STRING'' ''CHAR'') -> ''VECTOR_of_STRING''|''STRING''を''CHAR''で分割してベクタで返す。|
		["split-char"] = expr_split_char;
------
--DOC:| append | ('''append''' ''LIST'' ... ''LIST'') -> ''LIST''|''LIST''を連結してリストにする。|
		["append"] = expr_append;
--DOC:| reverse | ('''reverse''' ''LIST'') -> ''LIST''|''LIST''の要素を逆順にしたリストを返す。|
		["reverse"] = expr_reverse;
------
--DOC:| < | ('''<''' ''NUMBER'' ''NUMBER''...) -> ''BOOL'' |1番目のパラメータと2番目のパラメータを数値に変換して比較し、1番目のパラメータが小さい時trueを返す。|
		["<"] = expr_nlt;
--DOC:| <= | ('''<=''' ''NUMBER'' ''NUMBER''...) -> ''BOOL'' |1番目のパラメータと2番目のパラメータを数値に変換して比較し、1番目のパラメータが大きくない時trueを返す。|
		["<="] = expr_nle;
--DOC:| > | ('''>''' ''NUMBER'' ''NUMBER''...) -> ''BOOL'' |1番目のパラメータと2番目のパラメータを数値に変換して比較し、1番目のパラメータが大きい時trueを返す。|
		[">"] = expr_ngt;
--DOC:| >= | ('''>=''' ''NUMBER'' ''NUMBER''...) -> ''BOOL'' |1番目のパラメータと2番目のパラメータを数値に変換して比較し、1番目のパラメータが小さくない時trueを返す。|
		[">="] = expr_nge;
--DOC:| = | ('''=''' ''NUMBER'' ''NUMBER''...) -> ''BOOL''|1番目のパラメータと2番目のパラメータを数値に変換して比較し、一致するときtrueを返す。|
		["="] = expr_nequal;
--DOC:| != | ('''!=''' ''NUMBER'' ''NUMBER''...) -> ''BOOL''| (not (= ''OBJECT'' ''OBJECT''))|
		["!="] = expr_notnequal;
------
--DOC:| lt | ('''lt''' ''STRING'' ''STRING''...) -> ''BOOL''|1番目のパラメータと2番目のパラメータを比較し、1番目のパラメータが小さい時trueを返す。|
		["lt"] = expr_lt;
--DOC:| le | ('''le''' ''STRING'' ''STRING''...) -> ''BOOL''|1番目のパラメータと2番目のパラメータを比較し、1番目のパラメータが大きくない時trueを返す。|
		["le"] = expr_le;
--DOC:| gt | ('''gt''' ''STRING'' ''STRING''...) -> ''BOOL''|1番目のパラメータと2番目のパラメータを比較し、1番目のパラメータが大きい時trueを返す。|
		["gt"] = expr_gt;
--DOC:| ge | ('''ge''' ''STRING'' ''STRING''...) -> ''BOOL''|1番目のパラメータと2番目のパラメータを比較し、1番目のパラメータが小さくない時trueを返す。|
		["ge"] = expr_ge;
--DOC:| eq |('''eq''' ''STRING'' ''STRING''...) -> ''BOOL'' |1番目のパラメータと2番目のパラメータが文字列として一致するオブジェクトのときtrueを返す。|
		["eq"] = expr_streq;
--DOC:| neq | ('''neq''' ''STRING'' ''STRING''...) -> ''BOOL''|(not (eq ''STRING'' ''STRING''))|
		["neq"] = expr_notstreq;
------
--DOC:| == | ('''==''' ''OBJECT'' ''OBJECT''...) -> ''BOOL'' |1番目のパラメータと2番目のパラメータが一致するオブジェクトのときtrueを返す。|
		["=="] = expr_eq;
--DOC:| !== | ('''!==''' ''OBJECT'' ''OBJECT''...) -> ''BOOL''|(not (== ''OBJECT'' ''OBJECT''))|
		["!=="] = expr_neq;
--DOC:| equal| ('''equal''' ''OBJECT'' ''OBJECT''...) -> ''BOOL''|1番目のパラメータと2番目のパラメータが合同のオブジェクトのときtrueを返す。|
		["equal"] = expr_equal;
--DOC:| nequal| ('''nequal''' ''OBJECT'' ''OBJECT''...) -> ''BOOL''| (not (equal ''OBJECT'' ''OBJECT''))|
		["nequal"] = expr_notequal;
--DOC:| and |('''and''' ''BOOL'' ''BOOL''...) -> ''BOOL''|パラメータが全てtrueの時、trueを返す。1番目のパラメータから順に評価し、falseが現れた時、以降のパラメータは評価しない。|
		["and"] = expr_and;
--DOC:| or |('''or''' ''BOOL'' ''BOOL''...) -> ''BOOL''|パラメータが全てfalseの時、falseを返す。1番目のパラメータから順に評価し、trueが現れた時、以降のパラメータは評価しない。|
		["or"] = expr_or;
--DOC:| not |('''not''' ''BOOL'') -> ''BOOL''|パラメータがfalseの時、trueを返す。|
		["not"] = expr_not;
--DOC:| nullp |('''nullp''' ''OBJECT''...) -> ''BOOL''|パラメータがnullの時、trueを返す。|
		["nullp"] = expr_nullp;
--DOC:| not-nullp |('''not-nullp''' ''OBJECT''...) -> ''BOOL''|パラメータがnullの時、falseを返す。|
		["not-nullp"] = expr_not_nullp;
--DOC:| emptyp |('''emptyp''' ''OBJECT''...) -> ''BOOL''|パラメータがnull、空文字列の時、trueを返す。|
		["emptyp"] = expr_emptyp;
--DOC:| not-emptyp |('''not-emptyp''' ''OBJECT''...) -> ''BOOL''|パラメータがnull、空文字列でない時、trueを返す。|
		["not-emptyp"] = expr_not_emptyp;
------
--DOC:| cond | ('''cond''' (''BOOL'' ''FUNCTION''...) ...) -> ''LAST_VALUE'' |条件が成立した項のファンクションを実行する。|
		["cond"] = expr_cond;
--DOC:| setvar | ('''setvar''' ''NAME'' ''VALUE'') -> ''VALUE'' <br> ('''setvar''' ''LIST'' [''LIST'' / ''VECTOR'']) |変数に値を保存する。|
		["setvar"] = expr_setvar;
--DOC:| getvar | ('''getvar''' ''NAME'' :parent ''INT'') -> ''VALUE'' | 変数から値を読み出す。|
		["getvar"] = expr_getvar;
--DOC:| setevar | ('''setevar''' ''NAME'' ''VALUE'') -> ''VALUE'' <br> ('''setevar''' ''LIST'' [''LIST'' / ''VECTOR'']) | E変数に値を保存する。|
		["setevar"] = expr_setevar;
--DOC:| getevar | ('''getevar''' ''NAME'' :parent ''INT'') -> ''VALUE'' | E変数から値を読み出す。|
		["getevar"] = expr_getevar;
--DOC:| progn | ('''progn''' ''FUNC''...) |FUNCを実行する。|
		["progn"] = expr_progn;
--DOC:| lambda | ('''lambda''' (''PARAMS''...) FUNC...) |ファンクション定義。|
		["lambda"] = expr_lambda;
--DOC:| apply | ('''apply''' ''SYMBOL'' ''OBJ''... ''LIST'') -> ''OBJ''|''SYMBOL''にバインドされたファンクションを実行する。|
		["apply"] = expr_apply;
--DOC:| vector-each | ('''vector-each''' ''VAR'' ''VECTOR'' ''EXPR''...) -> ''LAST_VALUE''|''VECTOR''の各要素を変数''VAR''に保存して、''EXPR''の実行を繰り返す。|
		["vector-each"] = expr_vector_each;
--DOC:| table-each | ('''table-each''' ''VAR_KEY'' ''VAR_VAL'' ''TABLE'' ''EXPR''...) -> ''LAST_VALUE''|''TABLE''の各要素を変数''VAR_KEY''、''VAR_VAL''に保存して、''EXPR''の実行を繰り返す。|
		["table-each"] = expr_table_each;
--DOC:| proc | ('''proc''' ''PROCESSOR''...) -> nil|パラメータを順に評価し、得られた''PROCESSOR''を順に実行する。|
		["proc"] = expr_proc;
--DOC:| vector-eval | ('''vector-eval''' ''VECTOR'') -> ''VECTOR''|''VECTOR''の各要素を評価したベクタを返す。|
		["vector-eval"] = expr_vector_eval;
--DOC:| table-eval | ('''table-eval''' ''TABLE'') -> ''TABLE''|''TABLE''の各要素を評価したテーブルを返す。|
		["table-eval"] = expr_table_eval;
--DOC:| reindex | ('''reindex''' ''DB'' ''ATTR'') -> nil |パラメータデー与えられたテーブルの属性のインデックスを再作成する。|
		["reindex"] = expr_reindex;
--DOC:| schema | ('''schema''') -> ''TABLE'' |スキーマ定義を出力する。|
		["schema"] = expr_schema;
------
----DOC:| sleep | ('''sleep''' ''SECOND'') -> nil|スレッドの実行を休止する。DEBUGモード時のみ。|
--		["sleep"] = expr_sleep;
------
--DOC:
--DOC:==concurrentファンクション
--DOC:*concurrentファンクションは、主にprognコマンドの_evalパラメータか、スクリプト関数の:procオプションなどに指定する。
--DOC:*concurrentファンクションの戻り値は、関数オブジェクトである。
--DOC:*関数オブジェクトを実行すると、BOOL値を出力する。
--DOC:*concurrentファンクションのパラメータの
--DOC:*add関数、key-get関数やconproc関数の:varオプションは、関数内で有効なローカル変数を定義する。
--DOC:*ローカル変数「_parent」から上位のブロックの変数にアクセスできる。
--DOC:
--DOC:
--DOC:+ 記法について
--DOC:+* パラメータに指定するオブジェクトは斜体で書く。
--DOC:+* キーワードは通常の立体字で書く。
--DOC:+* 「#」で始まるキーワードは、オプションパラメータ。必要に応じて指定する。
--DOC:+* 「:」で始まるキーワードは、パラーメタを１つ取るオプションパラメータ。必要に応じて指定する。
--DOC:+* concurrentファンクションの戻り値の関数オブジェクトを''PROCESSOR''と表記する。
--DOC:+* 斜体で、「''EXPR_''」で始まるパラメータは、concurrentファンクションの評価時には評価されず、関数オブジェクトを評価するときに評価される。
--DOC:
--DOC:
--DOC:
--DOC:
--DOC:|table:w=100%|t:c:w=14%|t:w=40%|t:|
--DOC:|h:ファンクション|h:パラメータ|h:説明|
--DOC:| output | ('''output''' ''EXPR_SELECTOR'' ... ''':store''' ''VAR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' | progn関数を繰り返し実行した結果を集約して、VECTORとして変数''VAR''に格納する。''EXPR_SELECTOR''はDBアクセス時に評価され、結果のVECTORの要素となる。''EXPR_SELECTOR''の評価結果がVECTOR型、TABLE型の時、それぞれVECTOR、TABLEの要素を評価して出力する。シンボルかCONSの時、評価して得られた値を出力する。storeパラメータで出力する変数を指定する。省略した場合は、変数outputに出力する。''EXPR_SELECTOR''が実行されなかった時、出力は何も追加されないベクタになる。|
		["output"] = cexpr_output;
--DOC:| output-table | ('''output-table''' ''EXPR_KEY'' ''EXPR_VALUE'' ... ''':store''' ''VAR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |progn関数を繰り返し実行した結果を集約して、TABLEとして変数''VAR''に格納する。|
		["output-table"] = cexpr_output_table;
--DOC:| count | ('''count''' ''VAR'' ''':every''' ''NUM'' ''':residue''' ''NUM'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコード数をカウントし、変数に格納する。変数は'output.countなどと指定する。:everyパラメータで指定した回数カウントするごとに:procパラメータで指定したconcurrentファンクションを実行する。カウント数を回数で割った剰余が:residueパラメータに一致する時、:procパラメータを実行する。:residueパラメータを省略すると、1が指定される。|
		["count"] = cexpr_count;
--DOC:| store | ('''store''' ''VAR'' ''EXPR_VALUE'' ... '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |値を変数に格納する。|
		["store"] = cexpr_store;
--DOC:| e-store | ('''e-store''' ''VAR'' ''EXPR_VALUE'' ... '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' | 値をE変数に格納するconcurrentファンクション。|
		["e-store"] = cexpr_e_store;
--DOC:| undef | ('''undef''' ''VAR''...) -> ''PROCESSOR'' |変数を削除するconcurrentファンクションを返す。|
		["undef"] = cexpr_undef;
--DOC:| e-undef | ('''e-undef''' ''VAR''...) -> ''PROCESSOR'' |E変数を削除するconcurrentファンクションを返す。|
		["e-undef"] = cexpr_e_undef;
--DOC:| select | ('''select''' ''EXPR_CONDITION'' ''':proc''' ''PROCESSOR'' ''':false-proc''' ''PROCESSOR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' ''':offset''' ''NUM'' '''#true''' '''#false''') -> ''PROCESSOR'' | シンボル_にバインドされているテーブルが、cond, limit, offsetの条件に合う場合、''PROCESSOR''に適用する。limitに達した時、次のキーを:nextオプションで指定した名前の変数に格納する。|
		["select"] = cexpr_select;
--DOC:| add | ('''add''' ''DB'' ''EXPR_KEY'' ''EXPR_TABLE'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':xt''' ''SEC'' ''':unique''' ''VECTOR_KEY'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコードを追加する。:storeオプションで指定した変数にプライマリキーが格納される。:storeオプション無指定の場合、変数「_」に格納される。変数はローカル変数として隔離される。|
		["add"] = cexpr_dbadd;
--DOC:| set | ('''set''' ''DB'' ''EXPR_KEY'' ''EXPR_TABLE'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':xt''' ''SEC'' ''':unique''' ''VECTOR_KEY'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコードを追加、更新する。|
		["set"] = cexpr_set;
--DOC:| update | ('''update''' ''DB'' ''EXPR_KEY'' ''EXPR_TABLE'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':xt''' ''SEC'' ''':unique''' ''VECTOR_KEY'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコードを更新する。|
		["update"] = cexpr_update;
--DOC:| increment | ('''increment''' ''DB'' ''EXPR_KEY'' ''EXPR_ATTR'' ''EXPR_VAL'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':xt''' ''SEC'' '''#true''' '''#false''') -> ''PROCESSOR'' |属性''EXPR_ATTR''の値に''EXPR_VAL''を加算する。''EXPR_VAL''を省略すると、1 加算される。|
		["increment"] = cexpr_increment;
--DOC:| decrement | ('''decrement''' ''DB'' ''EXPR_KEY'' ''EXPR_ATTR'' ''EXPR_VAL'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':xt''' ''SEC'' '''#true''' '''#false''') -> ''PROCESSOR'' |属性''EXPR_ATTR''の値に''EXPR_VAL''を減算する。''EXPR_VAL''を省略すると、1 減算される。|
		["decrement"] = cexpr_decrement;
--DOC:| del | ('''del''' ''DB'' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコードを削除する。|
		["del"] = cexpr_del;
--DOC:| index-iterate-del | ('''index-iterate-del''' ''DB'' ''ATTR'' ''EXPR_VALUE'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |インデックスからレコードを検索して削除する。index-iterateファンクションからdelファンクションを呼び出した場合、カーソルが正しくレコードを移動できない。#onceオプションをつけると、最初のマッチのみ実行する。|
--DOC:|^ index-iterate-del | ('''index-iterate-del''' ''DB'' '''['''''ATTR''...''']''' '''['''''EXPR_VALUE''...''']''' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |^|
		["index-iterate-del"] = cexpr_index_iterate_del;
--DOC:| pickoff | ('''pickoff''' ''DB'' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコードを取り出し、削除する。onceオプションを指定すると、concurrentファンクションとして1度だけ実行される。|
		["pickoff"] = cexpr_pickoff;
--DOC:| key-get | ('''key-get''' ''DB'' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコードを取り出す。onceオプションを指定すると、concurrentファンクションとして１度だけ実行される。|
		["key-get"] = cexpr_key_get;
--DOC:| key-iterate | ('''key-iterate''' ''DB'' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |レコード一覧の取得。|
		["key-iterate"] = cexpr_key_iterate;
--DOC:| index-get | ('''index-get''' ''DB'' ''ATTR'' ''EXPR_VALUE'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#true''' '''#false''') -> ''PROCESSOR'' |インデックス検索。属性''ATTR''は、属性名。インデックステーブルを選択する。''EXPR_VALUE''は、属性の値。''EXPR_VALUE''、''EXPR_KEY''はDBのアクセス時に評価される。最初のマッチのみ実行する。|
		["index-get"] = cexpr_index_get;
--DOC:| index-iterate | ('''index-iterate''' ''DB'' ''ATTR'' ''EXPR_VALUE'' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |インデックス検索。属性''ATTR''は、属性名。インデックステーブルを選択する。''EXPR_VALUE''は、属性の値。''EXPR_VALUE''、''EXPR_KEY''はDBのアクセス時に評価される。#onceオプションをつけると、最初のマッチのみ実行する。|
--DOC:|^| ('''index-iterate''' ''DB'' '''['''''ATTR''...''']''' '''['''''EXPR_VALUE''...''']''' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |複合インデックス検索。''ATTR_VECTOR''は、属性名のベクタ。''EXPR_VALUE_VECTOR''は属性値のベクタ。属性名のベクタより短いベクタを指定して検索できる。|
		["index-iterate"] = cexpr_index_iterate;
--DOC:| key-prefix | ('''key-prefix''' ''DB'' ''ATTR'' ''EXPR_VALUE'' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |キー検索。属性''ATTR''は、DBのキー、または、インデックステーブルを指定した属性名。|
		["key-prefix"] = cexpr_key_prefix;
--DOC:| index-prefix | ('''index-prefix''' ''DB'' ''ATTR'' ''EXPR_VALUE'' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |インデックス検索。属性''ATTR''は、DBのキー、または、インデックステーブルを指定した属性名。|
		["index-prefix"] = cexpr_index_prefix;
--DOC:| key-range | ('''key-range''' ''DB'' ''EXPR_VALUE_A'' ''EXPR_VALUE_B'' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |キーの値が''VALUE_A''から''VALUE_B''の範囲内にあるレコードを抽出する。|
		["key-range"] = cexpr_key_range;
--DOC:| index-range | ('''index-range''' ''DB'' ''ATTR'' ''EXPR_VALUE_A'' ''EXPR_VALUE_B'' '''#desc''' ''':proc''' ''PROCESSOR'' ''':start''' ''EXPR_KEY'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |属性''ATTR''の値が''VALUE_A''から''VALUE_B''の範囲内にあるレコードを抽出する。|
		["index-range"] = cexpr_index_range;
--DOC:| new-serial | ('''new-serial''' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''PROCESSOR'' |単純増加するシリアル番号を発行する。|
		["new-serial"] = cexpr_new_serial;
--DOC:| last-serial | ('''last-serial''' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''PROCESSOR'' |new-serialで最後に発行したシリアル番号を読み出す。|
		["last-serial"] = cexpr_last_serial;
--DOC:| reset-db-serial | ('''reset-db-serial''' ''DB'') -> ''PROCESSOR'' |''DB''のキーを走査し、new-serialで発行した最後のシリアル番号をシリアルDBに再登録する。|
		["reset-db-serial"] = cexpr_reset_db_serial;
--DOC:| dump-serial | ('''dump-serial''' '''#no-db''' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''TABLE'' <br> ('''dump-serial''' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''NUM'' <br> ('''dump-serial''' ''':db''' ''EXPR_DB'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#true''' '''#false''') -> ''NUM'' |シリアルDBのレコードを出力する。''KEY''を指定した場合、該当するレコードのシリアル番号を出力する。無指定の場合、全レコードをテーブルとして出力する。|
		["dump-serial"] = cexpr_dump_serial;
--DOC:| restore-serial | ('''restore-serial''' ''EXPR_KEY'' ''EXPR_NUM'') -> nil <br> ('''restore-serial''' ''':db''' ''EXPR_DB'' ''EXPR_NUM'') -> nil <br> ('''restore-serial''' ''EXPR_TABLE'') -> nil |シリアルDBのレコードを書き込む。''KEY''に文字列を指定した場合、''KEY''をキーとするレコードに''NUM''を書き込む。''NUM''がnilの場合、レコードを削除する。パラメータに''EXPR_TABLE''を指定した場合、複数レコードを更新する。|
		["restore-serial"] = cexpr_restore_serial;
--DOC:| pushmsg | ('''pushmsg''' ''DB'' ''EXPR_KEY'' ''EXPR_TABLE'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' ''':xt''' ''SEC'' ''':unique''' ''VECTOR_KEY'' '''#true''' '''#false''') -> ''PROCESSOR'' |メッセージキューにレコードを追加する。|
		["pushmsg"] = cexpr_pushmsg;
--DOC:| popmsg | ('''popmsg''' ''DB'' ''EXPR_KEY'' ''':store''' ''VAR'' ''':proc''' ''PROCESSOR'' '''#once''' ''':limit''' ''NUM'' ''':next''' ''VAR'' '''#true''' '''#false''') -> ''PROCESSOR'' |メッセージキューからレコードを取り出し、キューから削除する。|
		["popmsg"] = cexpr_popmsg;
--DOC:| coneval | ('''coneval''' ''EXPR''...) -> ''PROCESSOR'' |''EXPR''を実行するconcurrentファンクションを出力する。|
		["coneval"] = cexpr_coneval;
--DOC:| conproc | ('''conproc''' ''':var''' ''VARDEF'' ''':e-var''' ''VARDEF'' ''':break-if''' ''EXPR_BOOL'' ''':on-break''' ''PROCESSOR'' '''#break-if-limit''' '''#true''' '''#false''' ''PROCESSOR''...) -> ''PROCESSOR'' |PROCESSORを全て評価し、連続して実行するconcurrentファンクションを出力する。:varオプション、:e-varオプションで、変数名、変数名のリストを指定すると、ローカル変数として、変数、E変数を隔離する。:varオプション、e-var:オプションを指定しないと、ローカル環境を作らない。:break-ifオプションで指定した''EXPR''を各リストの実行に先立って実行し、成立したらリストの実行を中断する。|
		["conproc"] = cexpr_conproc;
--DOC:| local-var | ('''local-var''' ''VARDEF'') -> ''PROCESSOR'' | ローカル変数の定義。直前のローカル環境を作るconcurrentファンクションの環境内に変数を定義する。|
		["local-var"] = cexpr_local_var;
--DOC:| local-e-var | ('''local-e-var''' ''VARDEF'') -> ''PROCESSOR'' | ローカルのE変数の定義。直前のローカル環境を作るconcurrentファンクションの環境内に変数を定義する。|
		["local-e-var"] = cexpr_local_e_var;
--DOC:| conproc-vector-each | ('''conproc-vector-each''' ''VAR'' ''EXPR_VECTOR'' '''#break-if-limit''' ''PROCESSOR''...) -> ''PROCESSOR''|''EXPR_VECTOR''の各要素を変数''VAR''に保存して、''PROCESSOR''を実行するconcurrentファンクションを出力する。|
		["conproc-vector-each"] = cexpr_conproc_vector_each;
--DOC:| conproc-table-each | ('''conproc-table-each''' ''VAR_KEY'' ''VAR_VAL'' ''EXPR_TABLE'' '''#break-if-limit''' ''PROCESSOR''...) -> ''PROCESSOR''|''EXPR_TABLE''の各要素を変数''VAR''に保存して、''PROCESSOR''を実行するconcurrentファンクションを出力する。|
		["conproc-table-each"] = cexpr_conproc_table_each;
}

if DEBUG then
	optable["sleep"] = expr_sleep;
end

function pushEnv (tbl, env, fn)
	-- _parentを参照することで、上位の環境にアクセスできる。
	-- XXX _parentそのものは、mType属性が存在しないので、テーブル型として認識できない。
	if env[#env] then tbl[parentEnv] = env[#env] end
	table.insert (env, tbl)
	local ans = fn (env)
	env[#env][parentEnv] = nil
	table.remove (env, #env)
	return ans
end

function evalSym (e, env, eflag)		-- envはTable。mTypeのチェックは行わない
	local s = string.sub (e, 1, 1)
	if s == "#" or s == ":" then
		return {e, [mType] = kSymbol}
	end
	local a = kt.split (e, ".")
	local i = #env
	local p, w, v, q
	v = table.remove (a, 1)
	if string.sub (v, 1, 1) == kEVarPrefixCh then
		writeFnError (env, nil, v, "bad name")
		return nil
	end
	w = tonumber (v)
	if w then v = w + 1 end					-- 0始まり
	if eflag and #a == 0 then v = kEVarPrefix .. v end
	while i >= 1 do
		q = env[i][v]
		if q then
			p = q
			break
		end
		i = i - 1
	end
	for i, v in ipairs (a) do
		if string.sub (v, 1, 1) == kEVarPrefixCh then
			writeFnError (env, nil, v, "bad name")
			return nil
		end
		if p then
			local w = tonumber (v)
			if w then v = w + 1 end			-- 0始まり
			if type (p) == "table" then
				if eflag and i == #a then v = kEVarPrefix .. v end
				p = p[v]
			else
				writeFnError (env, nil, e, "bad type. " .. stringJoinSub (kt.split (e, "."), ".", 1, i) .. "=" .. tdump (p))
			end
		end
	end
	return p
end

function refTSym_0 (name, env)
	local q, x
	local a = kt.split (name, ".")
	local k = table.remove (a, #a)
	local t = env[1]
	if k == "" then
		return t, nil
	end
	x = tonumber (k)
	if x then k = x + 1 end
	for i, v in ipairs (a) do
		x = tonumber (v)
		if x then v = x + 1 end
		q = t[v]
		if not q then
			q = {}
			t[v] = q
		end
		t = q
	end
	return t, k
end

function refTSym (name, env, eflag)
	local a = kt.split (name, ".")
	local i = #env
	local v = table.remove (a, 1)
	if string.sub (v, 1, 1) == kEVarPrefixCh then
		writeFnError (env, name, v, "bad name")
		return nil
	end
	local w = tonumber (v)
	if w then v = w + 1 end			-- 0始まり
    if eflag and #a == 0 then v = kEVarPrefix .. v end
	local e
	while i >= 1 do
		e = env[i]
		if e[v] then
			break
		end
		i = i - 1
	end
	if #a == 0 then
		return e, v
	else
		local k = table.remove (a, #a)
		if string.sub (k, 1, 1) == kEVarPrefixCh then
			writeFnError (env, name, k, "bad name")
			return nil
		end
		if k == "" then return nil end
		w = tonumber (k)
		if w then k = w + 1 end		-- 0始まり
		if eflag then k = kEVarPrefix .. k end
		if not e[v] then
			e[v] = {}
			e = e[v]
		else
			e = e[v]
			if type (e) ~= "table" then		-- チェックが厳密ではない
				writeFnError (env, name, tostring (v) .. " = " .. texpdump (e), "bad value")
				return nil
			end
		end
		for i, v in ipairs (a) do
			if string.sub (v, 1, 1) == kEVarPrefixCh then
				writeFnError (env, name, v, "bad name")
				return nil
			end
			w = tonumber (v)
			if w then v = w + 1 end		-- 0始まり
			if not e[v] then
				e[v] = {}
				e = e[v]
			else
				e = e[v]
				if type (e) ~= "table" then
					writeFnError (env, name, tostring (v) .. " = " .. texpdump (e), "bad value")
					return nil
				end
			end
		end
		return e, k
	end
end

function bindSym (name, val, env, eflag)	-- val=nilは変数を削除
	local t, k = refTSym (name, env, eflag)
	if t and k then
		t[k] = val
		if eflag then
			if DEBUG then debugLog ("[*" .. name .. " := " .. texpdump_short (val) .. "]") end
		else
			if DEBUG then debugLog ("[" .. name .. " := " .. texpdump_short (val) .. "]") end
		end
	end
end

function evalVector (e, env)
	local ans = {[mType] = kVector}
	for i, v in ipairs (e) do
		if consp (v) then
			-- リテラル内の関数の実行は安全でない
			ans[i] = safenil (v)
		else
			-- 要素内のベクタ、テーブルの展開は行わない
			ans[i] = safenil (evalExpr (v, env))
		end
	end
	return ans
end

function dupVector (e)
	local ans = {[mType] = kVector}
	for i, v in ipairs (e) do
		ans[i] = v
	end
	return ans
end

function evalTable (e, env)
	local ans = {[mType] = kTable}
	for k, v in pairs (e) do
		if string.sub (k, 1, 1) ~= kEVarPrefixCh then
			if consp (v) then
				-- リテラル内の関数の実行は安全でない
				ans[k] = safenil (v)
			else
				-- 要素内のベクタ、テーブルの展開は行わない
				ans[k] = safenil (evalExpr (v, env))
			end
		end
	end
	return ans
end

function dupTable (e)
	local ans = {[mType] = kTable}
	for k, v in pairs (e) do
		if string.sub (k, 1, 1) ~= kEVarPrefixCh then
			ans[k] = v
		end
	end
	return ans
end

function evalVTF (e, env)
	if vectorp (e) then
		return evalVector (e, env)
	elseif tablep (e) then
		return evalTable (e, env)
	else
		return evalFunc (e, env)
	end
end

function parseParams (parms, env)
	local e = parms
	local a
	local palist = {}
	local kwlist = {}
	local o
	while consp (e) do
		a = e.car
		e = e.cdr
		if symbolp (a) then
			s = a[1]
			if s == "&key" then
				o = kwlist
			elseif s == "&rest" then
				if consp (e) then
					a = e.car
					e = parms.cdr
					if symbolp (a) then
						return palist, kwlist, a[1]
					end
				end
				return palist, kwlist
			elseif o then
				kwlist[s] = true
			else
				table.insert (palist, s)
			end
		else
			writeFnError (env, cmd, a, typeError)
		end
	end
	return palist, kwlist
end

function evalLambda (cmd, args, env)
	if DEBUG then debugLogExp (texpdump (cmd) .. " " .. texpdump (args)) end
	local e = cmd.cdr
	local palist, kwlist, restarg = parseParams (e.car, env)
	e = e.cdr

	local a, s, f, ans
	local kwenv = {}
	while consp (args) do
		a = args.car
		args = args.cdr
		if symbolp (a) then
			s = string.sub (a[1], 1, 1)
			if s == ":" then
				s = string.sub (a[1], 2)
				if kwlist then
					f = kwlist[s]
					if f then
						kwenv[s] = evalExpr (args.car, env)
						args = args.cdr
						goto Lp1
					elseif f ~= nil then
						kwenv[s] = args.car
						args = args.cdr
						goto Lp1
					end
				end
				writeFnError (env, cmd, a[1], paramError)
				return nil			-- exitしろ
			elseif s == "#" then
				s = string.sub (a[1], 2)
				if kwlist then
					f = kwlist[s]
					if f ~= nil then
						kwenv[s] = true
						goto Lp1
					end
				end
				writeFnError (env, cmd, a[1], paramError)
				return nil			-- exitしろ
			end
		end
		f = table.remove (palist, 1)
		if f then
			kwenv[f] = evalExpr (a)
		else
			if restarg then
				local r
				local o = {}
				o.car = evalExpr (a, env)
				r = o
				while consp (args) do
					a = args.car
					args = args.cdr
					o.cdr = {car = evalExpr (a, env)}
					o = o.cdr
				end
				kwenv[restarg] = r
			end
			break
		end
		::Lp1::
	end
	pushEnv (kwenv, env, function (env)
							while consp (e) do
								a = e.car
								e = e.cdr
								ans = evalExpr (a, env)
							end
						end)
	return ans
end

function evalFunc (e, env)
	return evalExpr (e, env)
end

function evalExpr (e, env)	-- lambdaは自身を返す
	if e and type (e) == "table" then
		local t = e[mType]
		if not t then		-- Cons
			local op = e.car
			if symbolp (op) then
				local fn = optable[op[1]]
				if fn then
					if DEBUG then if not quotep (e) then debugLogExp (texpdump_short (e)) end end
					return fn (e, env)
				else
					writeFnError (env, e, nil, fnError)
				end
			elseif lambdap (op) then
				return evalLambda (op, e.cdr, env)
			end
			return {}		-- nil
		elseif t == kSymbol then
			return evalSym (e[1], env)
		elseif t == kVector then
			return dupVector (e)
		elseif t == kTable then
			return dupTable (e)
		else
			return e
		end
	else
		return e
	end
end

------------------------------------------------------------
function serial_new (key)
	if serialdb then
		if key then
			key = tostring (key)
		else
			key = "-"
		end
		return (serialdb:increment (key .. sid, 1))
	else
		kt.log ("error", "serialdb not defined.")
		return nil
	end
end

function serial_last (key)
	if serialdb then
		if key then
			key = tostring (key)
		else
			key = "-"
		end
		return (serialdb:increment (key .. sid, 0))
	else
		return nil
	end
end

function db_serial_reset (db)
	if serialdb then
		local key
		key = db:path () .. sid
		if serialdb:check (key) < 0 then
			return
		end
		db:begin_transaction ()
		local cur = db:cursor ()
		local rc = cur:jump ()
		local num = 0
		while rc do
			key = deserialkey (cur:get_key ())
			if key and key > num then
				num = key
			end
			rc = cur:step ()
		end
		cur:disable ()
		db:end_transaction ()
		-- XXX レーシングを起こす恐れあり
		key = db:path () .. sid
		serialdb:remove (key)
		serialdb:increment (key, 0, num)
	else
		kt.log ("error", "no serial db")
	end
end

function db_index_set_item_t (key, idxdbdb, val, xt)
	if not idxdbdb:set (val .. kNUL .. key, key, xt) then
		kt.log ("error", "adding an index entry failed")
	end
end

function db_index_set_item (key, idxspec, val, xt)
	if idxspec and val then
		db_index_set_item_t (key, idxspec.db, val, xt)
	end
end

function db_index_del_item_t (key, idxdbdb, val)	-- valがnilはエラー
	local i = val .. kNUL .. key
	if not idxdbdb:remove (i) then
		kt.log ("error", "removing an index entry failed")
	end
end

function db_index_del_item (key, idxspec, val)	-- valがnilはエラー
	if idxspec and val then
		db_index_del_item_t (key, idxspec.db, val)
	end
end

function index_join (list, ch)
	local ans
	for i, v in ipairs (list) do
		if nullp (v) then
			return nil
		end
		if i == 1 then
			ans = t_to_string (v)
		else
			ans = ans .. ch .. t_to_string (v)
		end
	end
	return ans
end

function idxspecSearch (idxdb, attrs)
	if type (attrs) ~= "table" then return nil end
	local key = index_join (attrs, "+")
	local ans = idxdb[key]
	if ans then
		return ans
	end
	key = key .. "+"
	local n = string.len (key)
	for k, v in pairs (idxdb) do
		if string.sub (k, 1, n) == key then
			return v
		end
	end
	return nil
end

function index_val (idxspec, obj)	-- 8.2 updated
	local val, type
	for i, attrspec in ipairs (idxspec.attrspecs) do
		local v = obj[attrspec[1]]
		if nullp (v) then
			return nil		-- attrspecsの全ての要素の属性を持たない場合はnil
		end
		type = attrspec[2]
		if type == kInteger then
			v = kt.e64 (v)
		elseif type == kNumber then
			v = kt.e64f (v)
		end
		if i == 1 then
			val = v
		else
			val = val .. kNUL .. v
		end
	end
	return val
end

function index_val_col (idxspec, n, obj)
	local val, type
	for i, attrspec in ipairs (idxspec.attrspecs) do
		local v = obj[attrspec[1]]
		if nullp (v) then
			return nil		-- attrspecsの全ての要素の属性を持たない場合はnil
		end
		type = attrspec[2]
		if type == kInteger then
			v = kt.e64 (v)
		elseif type == kNumber then
			v = kt.e64f (v)
		end
		if i == 1 then
			val = v
		else
			val = val .. kNUL .. v
		end
		if i >= n then return val end
	end
	return val
end

function db_index_set (db, key, obj, xt)
	for cattr, idxspec in pairs (idx[db]) do
		local val = index_val (idxspec, obj)
		if val then
			db_index_set_item_t (key, idxspec.db, val, xt)
		end
	end
end

function db_index_del (db, key, obj, exdb)
	for cattr, idxspec in pairs (idx[db]) do
		if idxspec.db ~= exdb then
			local val = index_val (idxspec, obj)
			if val then
				db_index_del_item_t (key, idxspec.db, val)
			end
		end
	end
end

function index_key (attrspecs, mval)
	local ans = ""
	local type
	for i, v in ipairs (mval) do
		if nullp (v) then
			return nil		-- nullは検索しない
		end
		v = t_to_string (v)
		type = attrspecs[i][2]
		if type == kInteger then
			ans = ans .. kt.e64 (v) .. kNUL
		elseif type == kNumber then
			ans = ans .. kt.e64f (v) .. kNUL
		else
			ans = ans .. v .. kNUL
		end
	end
	return ans, type	-- ansはNUL終端
end

-- 属性値のリストをインデックス値とするレコードのキーをインデックステーブルから読み込む
function db_index_get (idxspec, mval, outfn, startkey, kwenv, env, cmd)
	local ans = true
	local rf2
	if not vectorp (mval) then kt.log ("error", "internal error in db_index_iterate.") return nil end	-- error
	if #mval == 0 then return ans end
	if #idxspec.attrspecs < #mval then writeFnError (env, cmd, nil, nIndexError) return ans end	-- 値ベクトルが少なくてもインデックス検索できる。startオプションは使えない
	local valz = index_key (idxspec.attrspecs, mval)
	if not valz then return ans end
	-- valzはNUL終端
	local cur = idxspec.db:cursor ()
	local rc
	if startkey then
		rc = cur:jump (valz .. startkey)
	else
		rc = cur:jump (valz)
	end
	if rc then
		local nvalz = string.len (valz)
		while string.sub (cur:get_key (), 1, nvalz) == valz do
			local key = cur:get_value ()
			if not key then break end
			rf2 = outfn (key)
			break
		end
	end
	cur:disable ()
	return ans
end

-- 属性値のリストをインデックス値とするレコードのキーをインデックステーブルから読み込む
function db_index_iterate (idxspec, mval, outfn, startkey, kwenv, env, cmd)		-- 8.2 updated
	local ans = true
	local rf2
	if not vectorp (mval) then kt.log ("error", "internal error in db_index_iterate.") return nil end	-- error
	if #mval == 0 then return ans end
	if #idxspec.attrspecs < #mval then writeFnError (env, cmd, nil, nIndexError) return ans end	-- 値ベクトルが少なくてもインデックス検索できる。startオプションは使えない
	local valz = index_key (idxspec.attrspecs, mval)
	if not valz then return ans end
	-- valzはNUL終端
	local cur = idxspec.db:cursor ()
	local rc
	if startkey then
		rc = cur:jump (valz .. startkey)
	else
		rc = cur:jump (valz)
	end
	if rc then
		local nvalz = string.len (valz)
		while string.sub (cur:get_key (), 1, nvalz) == valz do
			local key = cur:get_value ()
			if not key then break end
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			rf2 = outfn (key)
			ans = ans and rf2
			if not ans or not cur:step () then break end	-- XXX deleteするとカーソルがずれる
		end
	end
	cur:disable ()
	return ans
end

function db_index_iterate_desc (idxspec, mval, outfn, startkey, kwenv, env, cmd)		-- 8.2 updated
	local ans = true
	local rf2
	if not vectorp (mval) then kt.log ("error", "internal error in db_index_iterate_desc.") return nil end	-- error
	if #mval == 0 then return ans end
	if #idxspec.attrspecs < #mval then writeFnError (env, cmd, nil, nIndexError) return ans end
	local valz = index_key (idxspec.attrspecs, mval)
	if not valz then return ans end
	-- valzはNUL終端
	local cur = idxspec.db:cursor ()
	local rc
	if startkey then
		rc = cur:jump_back (valz .. startkey)
	else
		rc = cur:jump_back (valz .. kFF)
	end
	if rc then
		local nvalz = string.len (valz)
		while string.sub (cur:get_key (), 1, nvalz) == valz do
			local key = cur:get_value ()
			if not key then break end
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			rf2 = outfn (key)
			ans = ans and rf2
			if not ans or not cur:step_back () then break end
		end
	end
	cur:disable ()
	return ans
end

function db_index_iterate_del (idxspec, mval, keyattr, outfn, db, env, cmd, kwenv)
	local ans = true
	if not vectorp (mval) then kt.log ("error", "internal error in db_index_iterate.") return nil end	-- error
	if #mval == 0 then return ans end
	if #idxspec.attrspecs < #mval then writeFnError (env, cmd, nil, nIndexError) return ans end
	local valz = index_key (idxspec.attrspecs, mval)
	if not valz then return ans end
	-- valzはNUL終端
	local cur = idxspec.db:cursor ()
	local rc = cur:jump (valz)
	if rc then
		local nvalz = string.len (valz)
		while ans do
			rc = cur:get_key ()
			if not rc then break end
			if string.sub (rc, 1, nvalz) ~= valz then break end
			local key = cur:get_value ()
			if not key then break end
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			cur:remove ()		-- XXX hack
			local rc2, ans2 = op_dbdel (outfn, db, key, idxspec.db)
			ans = ans and ans2
		end
	end
	cur:disable ()
	return ans
end

function db_key_prefix (db, val, outfn, startkey, cmd, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	local keyattr = keynames[db]
	local cur = db:cursor ()
	local rc, key, valc
	local ans = true
	local rf2
	if startkey then
		rc = cur:jump (startkey)
	else
		rc = cur:jump (val)
	end
	if rc then
		local nval = string.len (val)
		while true do
			key = cur:get_key ()
			if string.sub (key, 1, nval) ~= val then break end	-- not match
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			valc = cur:get_value ()
			rf2 = getandmap (keyattr, outfn, key, valc)
			ans = ans and rf2
			if not ans or not cur:step () then break end
		end
	end
	cur:disable ()
	return ans
end

function db_key_prefix_desc (db, val, outfn, startkey, cmd, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	local keyattr = keynames[db]
	local cur = db:cursor ()
	local rc, key, valc
	local ans = true
	local rf2
	if startkey then
		rc = cur:jump_back (startkey)
	else
		rc = cur:jump_back (val .. kFF)
	end
	if rc then
		local nval = string.len (val)
		while true do
			key = cur:get_key ()
			if string.sub (key, 1, nval) ~= val then break end	-- not match
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			valc = cur:get_value ()
			rf2 = getandmap (keyattr, outfn, key, valc)
			ans = ans and rf2
			if not ans or not cur:step_back () then break end
		end
	end
	cur:disable ()
	return ans
end

function db_index_prefix (idxspec, mval, outfn, startkey, kwenv, env, cmd)
	local ans = true
	local rf2
	if not vectorp (mval) then kt.log ("error", "internal error in db_index_prefix.") return nil end	-- error
	if #mval == 0 then return ans end
	if #idxspec.attrspecs < #mval then writeFnError (env, cmd, nil, nIndexError) return ans end
	local valz, type = index_key (idxspec.attrspecs, mval)
	if not valz then return ans end
	local val = string.sub (valz, 1, -2)
	if type == kInteger or type == kNumber then		-- 数値は前方一致できない
		return
	end
	local cur = idxspec.db:cursor ()
	local rc
	if startkey then
		rc = cur:jump (valz .. startkey)		-- XXX***
	else
		rc = cur:jump (val)
	end
	if rc then
		local nval = string.len (val)
		while string.sub (cur:get_key (), 1, nval) == val do	-- 前方部分一致
			local key = cur:get_value ()
			if not key then break end
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			rf2 = outfn (key)
			ans = ans and rf2
			if not ans or not cur:step () then break end
		end
	end
	cur:disable ()
	return ans
end

function db_index_prefix_desc (idxspec, mval, outfn, startkey, kwenv, env, cmd)	-- 8.2 updated
	local ans = true
	local rf2
	if not vectorp (mval) then kt.log ("error", "internal error in db_index_prefix_desc.") return nil end	-- error
	if #mval == 0 then return ans end
	if #idxspec.attrspecs < #mval then writeFnError (env, cmd, nil, nIndexError) return ans end
	local valz, type = index_key (idxspec.attrspecs, mval)
	if not valz then return ans end
	local val = string.sub (valz, 1, -2)
	if type == kInteger or type == kNumber then		-- 数値は前方一致できない
		return
	end
	local cur = idxspec.db:cursor ()
	local rc
	if startkey then
		rc = cur:jump_back (valz .. startkey)		-- XXX********
	else
		rc = cur:jump_back (val .. kFF)
	end
	if rc then
		local nval = string.len (val)
		while string.sub (cur:get_key (), 1, nval) == val do		-- 前方部分一致
			local key = cur:get_value ()
			if not key then break end
			ans = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			rf2 = outfn (key)
			ans = ans and rf2
			if not ans or not cur:step_back () then break end
		end
	end
	cur:disable ()
	return ans
end

function db_index_range (idxspec, mvala, mvalb, outfn, startkey, mvalx, kwenv, env, cmd)
	local ans = true
	local rf2
	if (mvala and not vectorp (mvala))
		or (mvalb and not vectorp (mvalb))
		or (mvalx and not vectorp (mvalx)) then kt.log ("error", "internal error in db_index_range.") return nil end	-- error
	local valaz, valbz, valxz, cur, rc, rval
	if mvala then
		if #mvala == 0 then return ans end
		if #idxspec.attrspecs < #mvala then writeFnError (env, cmd, nil, nIndexError) return ans end
		valaz = index_key (idxspec.attrspecs, mvala)
		if not valaz then return ans end
	end
	if mvalb then
		if #mvalb == 0 then return ans end
		if #idxspec.attrspecs < #mvalb then writeFnError (env, cmd, nil, nIndexError) return ans end
		valbz = index_key (idxspec.attrspecs, mvalb)
		if not valbz then return ans end
		valbz = valbz .. kFF
	end
	if mvalx then
		if #mvalx == 0 then return ans end
		if #idxspec.attrspecs < #mvalx then writeFnError (env, cmd, nil, nIndexError) return ans end
		valxz = index_key (idxspec.attrspecs, mvalx)
		if not valxz then return ans end
	end
	cur = idxspec.db:cursor ()
	if startkey then
--
		writeFnError (env, cmd, nil, "start option is not implemented")
		return ans
--		rc = cur:jump (valxz .. startkey)
	elseif valaz then
		rc = cur:jump (valaz)
	else
		rc = cur:jump ()
	end
	if rc then
		while not valbz or cur:get_key () <= valbz do
			rval = cur:get_value ()
			if not rval then break end
			ans = procLimit (kwenv, cmd, rval, env)
			if kwenv._procbreak then break end
			rf2 = outfn (rval)
			ans = ans and rf2
			if not ans or not cur:step () then break end
		end
	end
	cur:disable ()
	return ans
end

function db_index_range_desc (idxspec, mvala, mvalb, outfn, startkey, mvalx, kwenv, env, cmd)
	local ans = true
	local rf2
	if (mvala and not vectorp (mvala))
		or (mvalb and not vectorp (mvalb))
		or (mvalx and not vectorp (mvalx)) then kt.log ("error", "internal error in db_index_range_desc.") return nil end	-- error
	local valaz, valbz, valxz, cur, rc, rval
	if mvala then
		if #mvala == 0 then return ans end
		if #idxspec.attrspecs < #mvala then writeFnError (env, cmd, nil, nIndexError) return ans end
		valaz = index_key (idxspec.attrspecs, mvala)
		if not valaz then return ans end	  -- 指定がエラーの場合、終了
	end
	if mvalb then
		if #mvalb == 0 then return ans end
		if #idxspec.attrspecs < #mvalb then writeFnError (env, cmd, nil, nIndexError) return ans end
		valbz = index_key (idxspec.attrspecs, mvalb)
		if not valbz then return ans end
	end
	if mvalx then
		if #mvalx == 0 then return ans end
		if #idxspec.attrspecs < #mvalx then writeFnError (env, cmd, nil, nIndexError) return ans end
		valxz = index_key (idxspec.attrspecs, mvalx)
		if not valxz then return ans end
	end
	cur = idxspec.db:cursor ()
	if startkey then
		rc = cur:jump_back (valxz .. startkey)		-- XXX***
	elseif valaz then
		rc = cur:jump_back (valaz .. kFF)
	else
		rc = cur:jump_back ()
	end
	if rc then
		while not valbz or cur:get_key () >= valbz do
			rval = cur:get_value ()
			if not rval then break end
			ans = procLimit (kwenv, cmd, rval, env)
			if kwenv._procbreak then break end
			rf2 = outfn (rval)
			ans = ans and rf2
			if not ans or not cur:step_back () then break end
		end
	end
	cur:disable ()
	return ans
end

function pickdb (name)
	if name then
		local db
		db = dbs[name]
		if not db then
			kt.log ("error", name .. ": no such db.")
		end
		return db
	else
		return db1
	end
end

------------------------------------------------------------
function serialkey (num)
	return string.sub (kt.e64 (os.time () - 1262304000), -6) .. string.sub (kt.e64 (num), -9) .. sid
end

function deserialkey (str)
	if string.sub (str, - sid_len) ~= sid then
		return nil
	end
	local m = string.sub (str, 7, - sid_len - 1)
	if string.len (m) ~= 9 then
		return nil
	end
	if DEBUG then print ("str:"..str..", m:"..m .. ", val:" .. tostring (kt.d64 ("80" .. m))) end
	return kt.d64 ("80" .. m)
end

-- objは、STRING=>STRING形式
function op_dbadd (outfn, db, key, obj, xt, uniqmattr, env, cmd)
	-- outmap: [STRING]: Vector
	local rf = true
	obj = t_to_table_nilfree (obj)
	if not key then
		if dbtype[db] == kNumber then
			key = serial_new (db:path ())
		else
			key = serialkey (serial_new (db:path ()))
		end
		if not key then
			kt.log ("error", "no serial db")
			return kt.RVEINVALID
		end
	end
	local idxspec, ukeylen
	if vectorp (uniqmattr) then
		ukeylen = #uniqmattr
		idxspec = idxspecSearch (idx[db], uniqmattr)
		if not idxspec then
			writeFnError (env, cmd, texpdump (uniqmattr), indexError)
			return kt.RVEINVALID
		end
	end
	local function visit (vkey, value)
		if idxspec then
			if DEBUG then debugLog ("unique " .. texpdump (uniqmattr)) end
			local v = index_val_col (idxspec, ukeylen, obj)
			if v then
				v = v .. kNUL
				local cur = idxspec.db:cursor ()
				local rc = cur:jump (v)
				if rc then
					rc = string.sub (cur:get_key (), 1, string.len (v)) == v
				end
				cur:disable ()
				if rc then
					key = nil
					if DEBUG then debugLogt ("unique break") end
					return kt.Visitor.NOP		-- unique制約
				end
			end
		end
		if value then
			key = nil
			return kt.Visitor.NOP		-- レコードがある場合、エラー
		end
		obj.mt = kt.time ()
		-- mapdumpは、テキストと数値型を区別しない
		local mobj = kt.mapdump (obj)
		obj[keynames[db]] = vkey
		db_index_set (db, vkey, obj, xt)
		return mobj, xt
	end
	--
	if not db:accept (key, visit) then
		kt.log ("error", "inserting a record failed")
		return kt.RVEINTERNAL
	end
	if key and outfn then
		rf = outfn:next (nil, key)	-- 繰り返しではないので、nextvarをセットする必要はない
	end
	return kt.RVSUCCESS, rf
end

function op_dbset (outfn, db, key, obj, xt, uniqmattr, env, cmd)
	-- outmap: [STRING]: Vector
	local rf = true
	obj = t_to_table_nilfree (obj)
	if not key then
		key = serialkey (serial_new (db:path ()))
		if not key then
			kt.log ("error", "no serial db")
			return kt.RVEINVALID
		end
	end
	local idxspec, ukeylen
	if vectorp (uniqmattr) then
		ukeylen = #uniqmattr
		idxspec = idxspecSearch (idx[db], uniqmattr)
		if not idxspec then
			writeFnError (env, cmd, texpdump (uniqmattr), indexError)
			return kt.RVEINVALID
		end
	end
	local function visit (vkey, value)
		if idxspec then
			if DEBUG then debugLog ("==> unique " .. texpdump (uniqmattr)) end
			local v = index_val_col (idxspec, ukeylen, obj)
			if v then
				v = v .. kNUL
				local cur = idxspec.db:cursor ()
				local rc = cur:jump (v)
				if rc then
					rc = string.sub (cur:get_key (), 1, string.len (v)) == v
					if rc then
						rc = cur:get_value () ~= vkey
					end
				end
				cur:disable ()
				if rc then
					key = nil
					if DEBUG then debugLog ("==> unique break") end
					return kt.Visitor.NOP		-- unique制約
				end
			end
		end
		if value then
			db_index_del (db, vkey, kt.mapload (value))
		end
		obj.mt = kt.time ()
		local mobj = kt.mapdump (obj)
		obj[keynames[db]] = vkey
		db_index_set (db, vkey, obj, xt)
		return mobj, xt
	end
	--
	if not db:accept (key, visit) then
		kt.log ("error", "inserting a record failed")
		return kt.RVEINTERNAL
	end
	if key and outfn then
		rf = outfn:next (nil, key)		-- nextvarをセットする必要はない
	end
	return kt.RVSUCCESS, rf
end

function op_dbupdate (outfn, db, key, obj, xt, uniqmattr, env, cmd)
	-- outmap: [STRING]: Vector
	local rf = true
	local idxspec, ukeylen
	if vectorp (uniqmattr) then
		ukeylen = #uniqmattr
		idxspec = idxspecSearch (idx[db], uniqmattr)
		if not idxspec then
			writeFnError (env, cmd, texpdump (uniqmattr), indexError)
			return kt.RVEINVALID
		end
	end
	local function visit (vkey, value)
		if value then
			local o = kt.mapload (value)
			local o2 = {}
			tcopy (o2, o)
			for attr, val in pairs (obj) do
				if attr == mType then
				elseif nullp (val) then
					o2[attr] = nil
				else
					o2[attr] = t_to_numstr (val)
				end
			end
			if idxspec then
				if DEBUG then debugLog ("==> unique " .. texpdump (uniqmattr)) end
				local v = index_val_col (idxspec, ukeylen, o2)
				if v then
					v = v .. kNUL
					local cur = idxspec.db:cursor ()
					local rc = cur:jump (v)
					if rc then
						rc = string.sub (cur:get_key (), 1, string.len (v)) == v
						if rc then
							rc = cur:get_value () ~= vkey
						end
					end
					cur:disable ()
					if rc then
						key = nil
						if DEBUG then debugLog ("==> unique break") end
						return kt.Visitor.NOP		-- unique制約
					end
				end
			end
			db_index_del (db, vkey, o)
			o2.mt = kt.time ()
			local mobj = kt.mapdump (o2)
			o2[keynames[db]] = vkey
			db_index_set (db, vkey, o2, xt)
			return mobj, xt
		else		-- レコードがない
			key = nil
			return kt.Visitor.NOP
		end
	end
	--
	if key then
		if not db:accept (key, visit) then
			kt.log ("error", "updating a record failed")
			return kt.RVEINTERNAL
		end
		if key and outfn then		-- レコードがある場合のみ
			rf = outfn:next (nil, key)		-- nextvarをセットする必要はない
		end
	end
	return kt.RVSUCCESS, rf
end

function op_increment (outfn, db, key, attr, delta, xt)
	-- outmap: [VALUE]:  Vector
	local rc = true
	if type (delta) ~= "number" then
		delta = 1
	end
	local nv
	local function visit (vkey, value)
		local o, v
		if value then
			local idxspec = idx[db][attr]
			o = kt.mapload (value)
			v = tonumber (o[attr])
			if not v then v = 0 end
			nv = v + delta
			db_index_del_item (vkey, idxspec, v)
			o[attr] = nv
			o.mt = kt.time ()
			db_index_set_item (vkey, idxspec, nv, xt)
			return kt.mapdump (o), xt
		else
			local idxspec = idx[db][attr]
			o = {}
			v = 0
			nv = v + delta
			o[attr] = nv
			o.mt = kt.time ()
			db_index_set_item (vkey, idxspec, nv, xt)
			return kt.mapdump (o), xt
		end
	end
	--
	if key then
		if not db:accept (key, visit) then
			kt.log ("error", "updating a record failed")
			return kt.RVEINTERNAL
		end
		if key and outfn then
			rc = outfn:next (nil, nv)		-- nextvarをセットする必要はない
		end
	end
	return kt.RVSUCCESS, rc
end

function op_decrement (outfn, db, key, attr, delta, xt)
	if type (delta) ~= "number" then
		delta = 1
	end
	return op_increment (outfn, db, key, attr, - delta, xt)
end

function op_dbdel (outfn, db, key, exdb)
	-- outmap: [STRING]: Vector
	local rf = true
	local function visit (vkey, value)
		if value then
			db_index_del (db, vkey, kt.mapload (value), exdb)
			return kt.Visitor.REMOVE
		else
			key = nil
			return kt.Visitor.NOP
		end
	end
	--
	if key then				-- nilがacceptでエラーになるが、無視する
		if not db:accept (key, visit) then
			kt.log ("error", "removing a record failed")
			return kt.RVEINTERNAL
		end
		if key and outfn then
			rf = outfn:next (nil, key)		-- nextvarをセットする必要はない
		end
	end
	return kt.RVSUCCESS, rf
end

function op_index_iterate_del (outfn, db, attr, val, cmd, env, kwenv)
	local rf = true
	local idxspec = idxspecSearch (idx[db], attr)
	local keyattr = keynames[db]
	if not idxspec then
		writeFnError (env, cmd, arraydump (attr), indexError)
		return kt.RVEINVALID
	end
--	db:begin_transaction ()		-- デッドロックする
	rf = db_index_iterate_del (idxspec, val, keyattr, outfn, db, env, cmd, kwenv)
--	db:end_transaction ()
	return kt.RVSUCCESS, rf
end

function op_pickoff (outfn, db, key)
	-- outmap: [TABLE]: Vector
	local rf = true
	local obj
	local function visit (vkey, value)
		if value then
			obj = kt.mapload (value)
			db_index_del (db, vkey, obj)
			obj[keynames[db]] = vkey	-- キーを出力する
			obj[mType] = kTable
			return kt.Visitor.REMOVE
		else
			key = nil
			return kt.Visitor.NOP
		end
	end
	--
	if key then
		if not db:accept (key, visit) then
			kt.log ("error", "removing a record failed")
			return kt.RVEINTERNAL
		end
		if key and obj and outfn then
			rf = outfn:next (nil, obj)		-- nextvarをセットする必要はない
		end
	end
	return kt.RVSUCCESS, rf
end

function op_key_get (outfn, db, key)
	-- キーがキーの属性に出力される
	-- outmap: [TABLE]: Vector
	local rf = true			-- ヒット無しは継続
	local value, xt
	if key then
		value, xt = db:get (key)
		if value then
			local obj = kt.mapload (value)
			obj[keynames[db]] = key
			obj[mType] = kTable
			if xt and xt < xtmax then
				obj.xt = xt - os.time ()
			end
			if outfn then
				rf = outfn:next (key, obj)
			end
		end
	end
	return kt.RVSUCCESS, rf
end

function op_key_iterate (outfn, db, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	if nullp (startkey) then startkey = nil end
	return op_key_range (outfn, db, startkey, nil, cmd, env, kwenv)
end

function op_key_iterate_desc (outfn, db, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	if nullp (startkey) then startkey = nil end
	return op_key_range_desc (outfn, db, startkey, nil, cmd, env, kwenv)
end

function getandmap (keyattr, outfn, key, val)
	if val then
		if outfn then
			local obj = kt.mapload (val)
			obj[keyattr] = key
			obj[mType] = kTable
			return outfn:next (key, obj)
		else
			return true
		end
	else
		return true
	end
end

function op_index_iterate_op (op, outfn, db, attr, val, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	local rf = true
	if nullp (startkey) then startkey = nil end
	local idxspec = idxspecSearch (idx[db], attr)
	local keyattr = keynames[db]
	if not idxspec then
		writeFnError (env, cmd, arraydump (attr), indexError)
		return kt.RVEINVALID
	end
--	db:begin_transaction ()		-- デッドロックする
--	rf = op (idxspec, val, function (key) return getandmap (keyattr, outfn, key, db:get (key)) end, startkey, fonce, env, cmd)
	rf = op (idxspec, val, function (key) return getandmap (keyattr, outfn, key, db:get (key)) end, startkey, kwenv, env, cmd)
--	db:end_transaction ()
	return kt.RVSUCCESS, rf
end

function op_index_get (outfn, db, attr, val, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, 
	return op_index_iterate_op (db_index_get, outfn, db, attr, val, startkey, cmd, env, kwenv)
end

function op_index_iterate (outfn, db, attr, val, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	return op_index_iterate_op (db_index_iterate, outfn, db, attr, val, startkey, cmd, env, kwenv)
end

function op_index_iterate_desc (outfn, db, attr, val, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	return op_index_iterate_op (db_index_iterate_desc, outfn, db, attr, val, startkey, cmd, env, kwenv)
end

function op_key_prefix_op (op, outfn, db, val, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	local rf = true
	if nullp (startkey) then startkey = nil end
	local keyattr = keynames[db]
	rf = op (db, val, outfn, startkey, cmd, kwenv)
	return kt.RVSUCCESS, rf
end

function op_key_prefix (outfn, db, val, startkey, cmd, env, kwenv)
	return op_key_prefix_op (db_key_prefix, outfn, db, val, startkey, cmd, env, kwenv)
end

function op_key_prefix_desc (outfn, db, val, startkey, cmd, env, kwenv)
	return op_key_prefix_op (db_key_prefix_desc, outfn, db, val, startkey, cmd, env, kwenv)
end

function op_index_prefix (outfn, db, attr, val, startkey, cmd, env, kwenv)
	return op_index_iterate_op (db_index_prefix, outfn, db, attr, val, startkey, cmd, env, kwenv)
end

function op_index_prefix_desc (outfn, db, attr, val, startkey, cmd, env, kwenv)
	return op_index_iterate_op (db_index_prefix_desc, outfn, db, attr, val, startkey, cmd, env, kwenv)
end

function op_key_range (outfn, db, vala, valb, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	local keyattr = keynames[db]
	local cur = db:cursor ()
	local rc, key, val
	local rf = true
	local rf2
	if vala then
		rc = cur:jump (vala)
	else
		rc = cur:jump ()
	end
	if rc then
		while true do
			key = cur:get_key ()
			if valb and key > valb then break end	-- not (key <= valb)
			rf = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			val = cur:get_value ()
			rf2 = getandmap (keyattr, outfn, key, val)
			rf = rf and rf2
			if DEBUG then debugProcVal (rf2) end
			if not rf or not cur:step () then break end
		end
	end
	cur:disable ()
	return kt.RVSUCCESS, rf
end

function op_key_range_desc (outfn, db, vala, valb, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	local keyattr = keynames[db]
	local cur = db:cursor ()
	local rc, key, val
	local rf = true
	local rf2
	if vala then
		rc = cur:jump_back (vala)
	else
		rc = cur:jump_back ()
	end
	if rc then
		while true do
			key = cur:get_key ()
			if valb and key < valb then break end	-- not (key >= valb)
			rf = procLimit (kwenv, cmd, key, env)
			if kwenv._procbreak then break end
			val = cur:get_value ()
			if not val then break end
			rf2 = getandmap (keyattr, outfn, key, val)
			rf = rf and rf2
			if DEBUG then debugProcVal (rf2) end
			if not rf or not cur:step_back () then break end
		end
	end
	cur:disable ()
	return kt.RVSUCCESS, rf
end

function op_index_range (outfn, db, attr, vala, valb, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	if nullp (startkey) then startkey = nil end
	local idxspec = idxspecSearch (idx[db], attr)
	local keyattr = keynames[db]
	if not idxspec then
		writeFnError (env, cmd, arraydump (attr), indexError)
		return kt.RVEINVALID
	end
	--
	local valx
	local rf = true
--	db:begin_transaction ()		-- デッドロックする
	if startkey then
		valx = db:get (startkey)
		if valx then
			valx = kt.mapload (valx)
			valx = valx[attr]
		else
			startkey = nil		-- 該当するレコードがない
		end
	end
	rf = db_index_range (idxspec, vala, valb,
						function (key) return getandmap (keyattr, outfn, key, db:get (key)) end,
						startkey, valx, kwenv, env, cmd)
--	db:end_transaction ()
	return kt.RVSUCCESS, rf
end

function op_index_range_desc (outfn, db, attr, vala, valb, startkey, cmd, env, kwenv)
	-- outmap: [TABLE ...]: Vector, "next" => NEXT_KEY: String
	if nullp (startkey) then startkey = nil end
	local idxspec = idxspecSearch (idx[db], attr)
	local keyattr = keynames[db]
	if not idxspec then
		writeFnError (env, cmd, arraydump (attr), indexError)
		return kt.RVEINVALID
	end
	--
	local valx
	local rf = true
--	db:begin_transaction ()		-- デッドロックする
	if startkey then
		valx = db:get (startkey)
		if valx then
			valx = kt.mapload (valx)
			valx = valx[attr]
		else
			startkey = nil		-- 該当するレコードがない
		end
	end
	rf = db_index_range_desc (idxspec, vala, valb,
						function (key) return getandmap (keyattr, outfn, key, db:get (key)) end,
						startkey, valx, kwenv, env, cmd)
--	db:end_transaction ()
	return kt.RVSUCCESS, rf
end

function op_newserial (outfn, key)
	-- outmap: [[VALUE]]: Vector
	-- keyにDBファイルのパスを指定すると衝突する。
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	local val = serial_new (key)
	if not val then
		return kt.RVEINVALID
	end
	local rf = true
	if outfn then
		rf = outfn:next (nil, val)
	end
	return kt.RVSUCCESS, rf
end

function op_lastserial (outfn, key)
	-- outmap: [[VALUE]]: Vector
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	local val = serial_last (key)
	local rf = true
	if not val then
		return kt.RVEINVALID
	end
	if outfn then
		rf = outfn:next (nil, val)
	end
	return kt.RVSUCCESS, rf
end

function unpackint64 (str)
	local val = kt.unpack ("CCCCCCCC", str)
	if val[1] >= 128 then
		local ans = 0
		for i, v in ipairs (val) do
			ans = ans * 256 + (255 - v)
		end
		return (- ans - 1)
	else
		return kt.unpack ("M", str)[1]
	end
end

function op_serial_get (outfn, key)
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	local rc = true
	local value = serialdb:get (key)
	if value and string.len (value) == 8 then
		value = unpackint64 (value)
		if outfn then
			rc = outfn:next (nil, value)
		end
	else
		-- 長さ8以外は想定外
	end
	return kt.RVSUCCESS, rc
end

function findDBByPath (spath)
	for k, v in pairs (kt.dbs) do
		if v:path () .. sid == spath then
			return v
		end
	end
	return nil
end

function op_serial_dump (outfn, nodb)
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	local rc = true
	serialdb:begin_transaction ()
	local cur = serialdb:cursor ()
	local rt = cur:jump ()
	local key, value
	local obj = {[mType] = kTable}
	if rt then
		while true do
			key = cur:get_key ()
			value = cur:get_value ()
			if nodb and findDBByPath (key) then
			else
				if value and string.len (value) == 8 then
					value = unpackint64 (value)
					obj[key] = value
				else
					-- 長さ8以外は想定外
				end
			end
			if not cur:step () then break end
		end
	end
	cur:disable ()
	serialdb:end_transaction ()
	if outfn then
		rc = outfn:next (nil, obj)
	end
	return kt.RVSUCCESS, rc
end

function op_restore_serial (key, val)
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	serialdb:remove (key)
	if val then
		serialdb:increment (key, 0, val)
	end
end

function op_restore_serial_table (tbl)
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	for key, val in pairs (tbl) do
		if string.sub (key, 1, 1) == kEVarPrefixCh then
		elseif nullp (val) then
			serialdb:remove (key)
		else
			serialdb:remove (key)
			serialdb:increment (key, 0, t_to_number (val))
		end
	end
end

function op_pushmsg (outfn, db, key, obj, xt, uniqmattr, env, cmd)
	-- outmap: [STRING]: Vector
	-- uniqmattrは、無視
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	if not key then
		return kt.RVEINVALID
	end
	local ikey
	local function visit (vkey, value)
		local o, v
		if value then
			o = kt.mapload (value)
			v = tonumber (o.push)
			if not v then v = 0 end
		else
			o = {pop = 0}
			v = 0
		end
		v = v + 1
		ikey = key .. "\t" .. tostring (v)
		o.push = v
		if not db:set (ikey, kt.mapdump (obj), xt) then
			kt.log ("error", "inserting a message record failed")
		end
		return kt.mapdump (o)
	end
	--
	if not serialdb:accept (key, visit) then
		kt.log ("error", "updating the queue failed")
		return kt.RVEINTERNAL
	end
	local rf = true
	if outfn then
		rf = outfn:next (nil, ikey)
	end
	return kt.RVSUCCESS, rf
end

function op_popmsg (outfn, db, key)
	-- outmap: [TABLE]: Vector
	if not serialdb then
		kt.log ("error", "no serial db")
		return kt.RVEINVALID
	end
	local ikey, obj
	local rf = true
	local function visit (vkey, value)
		local o, v, w, xt
		if value then
			o = kt.mapload (value)
			v = tonumber (o.pop)
			w = tonumber (o.push)
			if not v then v = 0 end
			if not w then w = 0 end
			if v < w then
				while v < w do
					v = v + 1
					ikey = key .. "\t" .. tostring (v)
					o.pop = v
					obj, xt = db:get (ikey)
					-- レコードがexpireしている場合がある
					if obj then
						db:remove (ikey)
						obj = kt.mapload (obj)
						obj[mType] = kTable
						if xt and xt < xtmax then
							obj.xt = xt - os.time ()
						end
						break
					end
				end
			end
		else
			o.push = 0
			o.pop = 0
		end
		return kt.mapdump (o)
	end
	--
	if not serialdb:accept (key, visit) then
		kt.log ("error", "updating the queue failed")
		return kt.RVEINTERNAL
	end
	if outfn then
		rf = outfn:next (key, obj)
	end
	return kt.RVSUCCESS, rf
end

function op_reindex (db, attr)
	local cur, rc, key, val, xt, obj
	local idxspec = idxspecSearch (idx[db], attr)
	if idxspec then
		idxspec.db:begin_transaction ()
		idxspec.db:clear ()
		cur = db:cursor ()
		rc = cur:jump ()
		if rc then
			while true do
				key, val, xt = cur:get (true)
				if key then
					obj = kt.mapload (val)
					obj[keynames[db]] = key
					val = index_val (idxspec, obj)
					if val then
						db_index_set_item_t (key, idxspec.db, val, xt)
					end
				else
					break
				end
			end
		end
		cur:disable ()
		idxspec.db:end_transaction ()
	end
	return kt.RVSUCCESS, true
end

function op_schema (outfn)
	-- outmap: [{"db" => TABLE_OF_VECTOR "index" => TABLE_OF_TABLE_OF_VECTOR "serial" => STRING "prefox" => STRING}]: Vector
	local ans = {[mType] = kTable}
	local db = {[mType] = kTable}
	local index = {[mType] = kTable}
	local dbname = {}
	-- db
	for k, v in pairs (dbs) do
		if k ~= "" then
			db[k] = {tfind (kt.dbs, v); k; keynames [v]; [mType] = kVector}
			dbname[v] = k
		end
	end
	ans.db = db
	-- index
	for k, v in pairs (idx) do
		for k2, v2 in pairs (v) do
			local d = dbname[k]
			if not index[d] then
				index[d] = {[mType] = kVector}
			end
			local e = {[mType] = kVector; tfind (kt.dbs, v2.db)}
			for i, v3 in ipairs (v2.attrspecs) do
				table.insert (e, {[mType] = kVector; v3[1]; typename (v3[2])})
			end
			table.insert (index[d], e)
		end
	end
	ans.index = index
	-- serial
	if serialdb then
		ans.serial = tfind (kt.dbs, serialdb)
	end
	-- suffix
	if sid ~= "" then
		ans.suffix = sid
	end
	-- SID
	ans.sid = tostring (kt.sid)
	local rf = true
	if outfn then
		rf = outfn:next1 (ans)
	end
	return kt.RVSUCCESS, rf
end

------------------------------------------------------------
----- scripts
--DOC:==スクリプト関数
--DOC:*Kyoto Tycoonの[[+http://fallabs.com/kyototycoon/spex.html TSV-RPCプロトコル]]を用いてアクセスする。
--DOC:*TSV-RPCで、play_scriptプロシージャを指定し、リクエストボディにパラメータデータを指定する。
--DOC:
--DOC:リクエスト例
--DOC:>
--DOC: POST /rpc/play_script HTTP/1.1
--DOC: Host: localhost:1978
--DOC: Content-Type: text/tab-separated-values
--DOC: Content-Length: 54
--DOC: 
--DOC: name	progn
--DOC: _eval	(key-iterate "User" :proc (output [_.ID _.Name _.Addr _.EMail]))
--DOC:<
--DOC:リプライ例
--DOC:>
--DOC: HTTP/1.1 200 OK
--DOC: Server: KyotoTycoon/0.9.56
--DOC: Date: Tue, 04 Sep 2015 03:00:27 GMT
--DOC: Content-Type: text/tab-separated-values
--DOC: 
--DOC: _1	["1" "野田佳彦" "千葉県船橋市" "noda@kantei.go.jp"]
--DOC:<
--DOC:
-- --DOC:|table:w=100%|t:w=20%|t:w=8%|t:w=25%|t:|
-- --DOC:|h:スクリプト関数名|h:説明/play_scriptパラメータ|<|<|

--DOC:
--DOC:===progn
--DOC:パラメータで与えたファンクションを実行する。
--DOC:|table:w=100%|c:m:w=8%|t:w=25%|t:|
--DOC:|h:I/O|h:TSV|h:説明|
--DOC:|IN|'''name''' '''progn'''|プロシージャ名。|
--DOC:|^|'''_eval''' ''FUNC'' ...|ファンクション列。S式で記述する。|
--DOC:|^|'''_env''' ''TABLE''|環境変数設定。拡張S式のテーブルで記述する。|
--DOC:|^|'''_debug''' ''BOOL''|デバッグ出力を指定する。|
--DOC:|OUT|...|環境変数'''output'''の値。|

function progn (inmap, outmap)
	-- in: _eval OBJ
	-- in: _env TABLE
	-- in: _debug BOOL
	-- out:
	local oDEBUG = DEBUG
	local eval = inmap.eval
	local env = texp (inmap.env)
	local expr
	if eval then
		expr = texplist (eval)
	end
	if not expr then
		return kt.RVSUCCESS
	end
	if nullp (env) then
		env = {}	-- [mType] = kTable は、含めない
	elseif not tablep (env) then
		kt.log ("error", "error in the env parameter")
		return kt.RVEINVALID
	else
		env[mType] = nil
	end
	if inmap.debug then
		DEBUG = 1
	end
	env[prognOutmap] = {[mType] = kVector}
	env[prognOutmapTable] = {[mType] = kTable}
	if DEBUG then print ("progn env:" .. envdump (env) .. ", eval:" .. texpdump (expr)) end
	--
	local rc
	while consp (expr) do
		local c = expr.car
		expr = expr.cdr
		local proc = evalExpr (c, {env})
		if consumerfnp (proc) then
			if DEBUG then debugLog ("progn", 1) end
			rc = proc:next (nil, nil)
			if DEBUG then debugProcVal (rc) end
			if DEBUG then debugLog ("progn end", -1) end
		end
	end
	if env[prognError] and type (env[prognOutmapTable]) == "table" then
		env[prognOutmapTable][prognError] = env[prognError]
	end
	output_texp (outmap, env[prognOutmap], env[prognOutmapTable]);
	DEBUG = oDEBUG
	return kt.RVSUCCESS
end

------------------------------------------------------------
----- main
if kt then
	initConf ()
	if sid == "" then
		kt.log ("error", "no serial suffix")
	else
		kt.log ("info", "serial suffix=" .. sid)
	end
end

--DOC:==問題
--DOC:*(output :store 'v v) で循環参照が発生する。
