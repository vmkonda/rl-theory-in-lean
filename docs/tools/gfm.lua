-- Pandoc filter: LaTeX write-ups -> GitHub-flavoured Markdown that matches the PDF.
--  * section-based theorem numbering (Theorem 2.1, ...) as in \newtheorem{theorem}{Theorem}[section]
--  * global equation numbers via \tag{n}, and resolved \ref / \eqref links
--  * section numbers in headings, with anchors for \label'd sections
--  * title, author, date and abstract as a header block
--  * GitHub-compatible math (no psmallmatrix, no italics spanning display math)

local thm_classes = {
  theorem = true, lemma = true, proposition = true, corollary = true, definition = true,
  assumption = true, fact = true, observation = true, remark = true,
}

local labels = {}      -- label -> displayed number
local sec, sub, thm, eqn, fig = 0, 0, 0, 0, 0

local function is_thm(div)
  for _, c in ipairs(div.classes) do
    if thm_classes[c] then return true end
  end
  return false
end

local function contains_display_math(inl)
  local found = false
  pandoc.walk_inline(inl, {
    Math = function(m) if m.mathtype == "DisplayMath" then found = true end end,
  })
  return found
end

-- Number equations, convert \begin{equation}\label{..}..\end{equation} into \tag.
local function fix_math(m)
  local t = m.text
  t = t:gsub("psmallmatrix", "pmatrix")
  t = t:gsub("\\qedhere", "")
  if m.mathtype == "DisplayMath" then
    local body = t:match("^%s*\\begin{equation}(.*)\\end{equation}%s*$")
    if body then
      eqn = eqn + 1
      local lab = body:match("\\label{([^}]*)}")
      if lab then labels[lab] = "(" .. eqn .. ")" end
      body = body:gsub("\\label{[^}]*}", "")
      t = body .. " \\tag{" .. eqn .. "}"
    end
  end
  m.text = t
  return m
end

-- Replace the number in the generated label ("Theorem 4" -> "Theorem 2.1").
local function renumber_label(div, number)
  local done = false
  return pandoc.walk_block(div, {
    Strong = function(s)
      if done then return nil end
      local txt = pandoc.utils.stringify(s)
      if txt:match("^%a+ %d+$") then
        done = true
        return pandoc.Strong(pandoc.Str(txt:gsub("%d+$", number)))
      end
    end,
    Emph = function(e)
      if done then return nil end
      local txt = pandoc.utils.stringify(e)
      if txt:match("^%a+ %d+$") then
        done = true
        return pandoc.Strong(pandoc.Str(txt:gsub("%d+$", number)))
      end
    end,
  })
end

-- Unwrap italics that contain display math (they would break GFM rendering).
local function unwrap_math_emph(blk)
  return pandoc.walk_block(blk, {
    Emph = function(e)
      if contains_display_math(e) then return e.content end
    end,
  })
end

local function slug_anchor(id)
  return pandoc.RawBlock("html", '<a id="' .. id .. '"></a>')
end

function Pandoc(doc)
  local out = {}
  -- pass 1: numbering
  for _, blk in ipairs(doc.blocks) do
    if blk.t == "Header" and not blk.classes:includes("unnumbered") then
      local num
      if blk.level == 1 then
        sec, sub, thm = sec + 1, 0, 0
        num = tostring(sec)
      elseif blk.level == 2 then
        sub = sub + 1
        num = sec .. "." .. sub
      end
      if num then
        if blk.identifier ~= "" then labels[blk.identifier] = num end
        if blk.identifier:find(":") then table.insert(out, slug_anchor(blk.identifier)) end
        table.insert(blk.content, 1, pandoc.Space())
        table.insert(blk.content, 1, pandoc.Str(num))
      end
      blk.level = blk.level + 1          -- the document title takes level 1
      blk.identifier = ""
      table.insert(out, blk)
    elseif blk.t == "Figure" then
      -- Markdown image plus a numbered caption paragraph (GitHub strips HTML figure math)
      fig = fig + 1
      if blk.identifier ~= "" then
        labels[blk.identifier] = tostring(fig)
        table.insert(out, slug_anchor(blk.identifier))
      end
      local img
      pandoc.walk_block(blk, { Image = function(i) img = img or i end })
      if img then
        img.attributes = {}
        table.insert(out, pandoc.Para({ img }))
      end
      local cap = pandoc.utils.blocks_to_inlines(blk.caption.long)
      local inl = { pandoc.Strong(pandoc.Str("Figure " .. fig .. ".")), pandoc.Space() }
      for _, x in ipairs(cap) do table.insert(inl, x) end
      table.insert(out, pandoc.Para(inl))
    elseif blk.t == "Div" and is_thm(blk) then
      thm = thm + 1
      local number = sec .. "." .. thm
      if blk.identifier ~= "" then labels[blk.identifier] = number end
      blk = renumber_label(blk, number)
      blk = unwrap_math_emph(blk)
      table.insert(out, blk)
    else
      table.insert(out, blk)
    end
  end
  doc.blocks = out
  doc = doc:walk({ Math = fix_math })
  -- pass 2: resolve references
  doc = doc:walk({
    Link = function(l)
      local kind = l.attributes["reference-type"]
      if kind then
        local key = l.attributes["reference"]
        local n = labels[key] or ("??" .. key)
        if kind == "eqref" and not n:match("^%(") then n = "(" .. n .. ")" end
        l.content = { pandoc.Str(n) }
        l.attributes["reference-type"] = nil
        l.attributes["reference"] = nil
      end
      return l
    end,
  })
  -- header block
  local head = {}
  if doc.meta.title then
    local title = pandoc.utils.blocks_to_inlines({ pandoc.Plain(doc.meta.title) })
    title = title:walk({ LineBreak = function() return pandoc.Space() end })
    table.insert(head, pandoc.Header(1, title))
  end
  local byline = {}
  if doc.meta.author then table.insert(byline, pandoc.utils.stringify(doc.meta.author)) end
  if doc.meta.date then table.insert(byline, pandoc.utils.stringify(doc.meta.date)) end
  if #byline > 0 then table.insert(head, pandoc.Para({ pandoc.Emph(table.concat(byline, " · ")) })) end
  table.insert(head, pandoc.Para({ pandoc.Emph(
    "Generated from the LaTeX source in this directory; the PDF has the same numbering.") }))
  if doc.meta.abstract then
    local abs = doc.meta.abstract
    local blocks = pandoc.utils.type(abs) == "Blocks" and abs or { pandoc.Para(abs) }
    local quoted = { pandoc.Para({ pandoc.Strong("Abstract.") }) }
    for _, b in ipairs(blocks) do table.insert(quoted, b) end
    table.insert(head, pandoc.BlockQuote(quoted))
  end
  for i = #head, 1, -1 do table.insert(doc.blocks, 1, head[i]) end
  doc.meta = {}
  return doc
end
