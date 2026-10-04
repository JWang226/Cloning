/* Progressive enhancement for the offline proof notebook. No requests or dependencies. */
(function () {
  "use strict";

  function ready(fn) {
    if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", fn, { once: true });
    else fn();
  }
  function normalize(value) {
    return String(value || "").normalize("NFKD").replace(/[\u0300-\u036f]/g, "").toLowerCase().replace(/\s+/g, " ").trim();
  }
  function resolveHref(url) {
    var value = String(url || "");
    if (/^(?:https?:|mailto:|#)/i.test(value)) return value;
    return String(window.PROOF_ROOT || "") + value.replace(/^\/+/, "");
  }
  function addHighlight(node, value, query) {
    var text = String(value || "");
    var needle = String(query || "").trim();
    var index = needle ? text.toLowerCase().indexOf(needle.toLowerCase()) : -1;
    if (index < 0) { node.textContent = text; return; }
    node.appendChild(document.createTextNode(text.slice(0, index)));
    var mark = document.createElement("mark");
    mark.textContent = text.slice(index, index + needle.length);
    node.appendChild(mark);
    node.appendChild(document.createTextNode(text.slice(index + needle.length)));
  }

  function initSearch() {
    var input = document.getElementById("site-search");
    var results = document.getElementById("search-results");
    if (!input || !results) return;
    var cachedSource = null;
    var records = [];
    var selected = -1;
    var links = [];
    var frame = 0;
    input.setAttribute("role", "combobox");
    input.setAttribute("aria-autocomplete", "list");
    input.setAttribute("aria-controls", "search-results");
    input.setAttribute("aria-expanded", "false");
    if (!input.hasAttribute("aria-label") && !input.labels.length) input.setAttribute("aria-label", "Search the proof notebook");
    input.setAttribute("autocomplete", "off");
    input.setAttribute("spellcheck", "false");
    results.setAttribute("role", "listbox");
    results.setAttribute("aria-label", "Search results");
    results.hidden = true;
    var status = document.createElement("span");
    status.className = "sr-only";
    status.setAttribute("role", "status");
    input.parentNode.appendChild(status);

    function close() {
      results.hidden = true;
      input.setAttribute("aria-expanded", "false");
      input.removeAttribute("aria-activedescendant");
      selected = -1;
      links.forEach(function (link) { link.setAttribute("aria-selected", "false"); });
    }
    function select(index) {
      if (!links.length) return;
      selected = (index + links.length) % links.length;
      links.forEach(function (link, i) { link.setAttribute("aria-selected", String(i === selected)); });
      input.setAttribute("aria-activedescendant", links[selected].id);
      links[selected].scrollIntoView({ block: "nearest" });
    }
    function getRecords() {
      var source = Array.isArray(window.PROOF_SEARCH) ? window.PROOF_SEARCH : [];
      if (source !== cachedSource) {
        cachedSource = source;
        records = source.map(function (item, index) {
          return {
            item: item, index: index,
            title: normalize(item.title), subtitle: normalize(item.subtitle),
            kind: normalize(item.kind), text: normalize(item.text)
          };
        });
      }
      return records;
    }
    function render() {
      var raw = input.value.trim();
      var query = normalize(raw);
      results.replaceChildren();
      links = [];
      selected = -1;
      input.removeAttribute("aria-activedescendant");
      if (!query) { status.textContent = ""; close(); return; }
      var terms = query.split(" ").filter(Boolean);
      var ranked = [];
      getRecords().forEach(function (record) {
        var haystack = record.title + " " + record.subtitle + " " + record.kind + " " + record.text;
        if (!terms.every(function (term) { return haystack.indexOf(term) !== -1; })) return;
        var score = record.title === query ? 150 : 0;
        if (record.title.indexOf(query) === 0) score += 70;
        else if (record.title.indexOf(query) !== -1) score += 45;
        if (record.subtitle.indexOf(query) !== -1) score += 20;
        terms.forEach(function (term) {
          if (record.title.indexOf(term) !== -1) score += 12;
          if (record.subtitle.indexOf(term) !== -1) score += 5;
          if (record.kind === term) score += 4;
        });
        ranked.push({ record: record, score: score });
      });
      ranked.sort(function (a, b) { return b.score - a.score || a.record.index - b.record.index; });
      ranked.slice(0, 9).forEach(function (match, i) {
        var item = match.record.item;
        var link = document.createElement("a");
        link.className = "search-result";
        link.id = "proof-search-option-" + i;
        link.href = resolveHref(item.url);
        link.setAttribute("role", "option");
        link.setAttribute("aria-selected", "false");
        var title = document.createElement("span");
        title.className = "search-result-title";
        addHighlight(title, item.title || "Untitled", raw);
        if (item.kind) {
          var kind = document.createElement("span");
          kind.className = "search-result-kind";
          kind.textContent = item.kind;
          title.appendChild(kind);
        }
        link.appendChild(title);
        if (item.subtitle) {
          var subtitle = document.createElement("span");
          subtitle.className = "search-result-subtitle";
          addHighlight(subtitle, item.subtitle, raw);
          link.appendChild(subtitle);
        }
        var text = String(item.text || "").replace(/\s+/g, " ");
        if (text) {
          var position = text.toLowerCase().indexOf(raw.toLowerCase());
          if (position < 0) position = text.toLowerCase().indexOf(terms[0]);
          var start = Math.max(0, position - 45);
          var excerpt = text.slice(start, start + 165);
          if (start) excerpt = "…" + excerpt;
          if (start + 165 < text.length) excerpt += "…";
          var description = document.createElement("span");
          description.className = "search-result-excerpt";
          addHighlight(description, excerpt, raw);
          link.appendChild(description);
        }
        link.addEventListener("pointerenter", function () { select(i); });
        link.addEventListener("click", close);
        results.appendChild(link);
        links.push(link);
      });
      if (!links.length) {
        var empty = document.createElement("p");
        empty.className = "search-empty";
        empty.textContent = "No results. Try a theorem name, chapter, or mathematical term.";
        results.appendChild(empty);
      }
      status.textContent = ranked.length ? ranked.length + " results. Use the arrow keys to choose a result." : "No search results.";
      results.hidden = false;
      input.setAttribute("aria-expanded", "true");
    }
    input.addEventListener("input", function () {
      window.cancelAnimationFrame(frame);
      frame = window.requestAnimationFrame(render);
    });
    input.addEventListener("focus", function () { if (input.value.trim()) render(); });
    input.addEventListener("keydown", function (event) {
      if (event.key === "Escape") { close(); event.preventDefault(); return; }
      if (event.key === "ArrowDown" || event.key === "ArrowUp") {
        event.preventDefault();
        if (results.hidden) render();
        select(selected < 0 ? (event.key === "ArrowDown" ? 0 : links.length - 1) : selected + (event.key === "ArrowDown" ? 1 : -1));
      } else if (event.key === "Enter" && !results.hidden && links.length) {
        event.preventDefault();
        links[selected < 0 ? 0 : selected].click();
      } else if (event.key === "Tab") close();
    });
    document.addEventListener("pointerdown", function (event) {
      if (event.target !== input && !results.contains(event.target)) close();
    });
    document.addEventListener("keydown", function (event) {
      var target = event.target;
      var editing = target && (target.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(target.tagName));
      if ((event.key === "/" && !editing) || ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === "k")) {
        event.preventDefault(); input.focus(); input.select();
      }
    });
  }

  function initMobileNav() {
    var toggle = document.getElementById("nav-toggle");
    var sidebar = document.querySelector(".sidebar");
    if (!toggle || !sidebar) return;
    if (!sidebar.id) sidebar.id = "site-navigation";
    toggle.setAttribute("aria-controls", sidebar.id);
    toggle.setAttribute("aria-expanded", "false");
    if (!toggle.hasAttribute("aria-label")) toggle.setAttribute("aria-label", "Toggle chapter navigation");
    var narrow = window.matchMedia("(max-width: 860px)");
    function setOpen(open, restoreFocus) {
      document.body.classList.toggle("mobile-nav-open", open);
      toggle.setAttribute("aria-expanded", String(open));
      sidebar.inert = narrow.matches && !open;
      if (open) {
        var first = sidebar.querySelector("a[aria-current='page'], a.active, a, button");
        if (first) first.focus({ preventScroll: true });
      } else if (restoreFocus) toggle.focus({ preventScroll: true });
    }
    toggle.addEventListener("click", function () { setOpen(!document.body.classList.contains("mobile-nav-open"), false); });
    sidebar.addEventListener("click", function (event) { if (event.target.closest("a") && narrow.matches) setOpen(false, false); });
    document.addEventListener("keydown", function (event) {
      if (event.key === "Escape" && document.body.classList.contains("mobile-nav-open")) setOpen(false, true);
      if (event.key === "Tab" && document.body.classList.contains("mobile-nav-open")) {
        var items = Array.prototype.slice.call(sidebar.querySelectorAll("a[href], button:not([disabled]), input:not([disabled]), [tabindex='0']"));
        if (!items.length) return;
        var first = items[0], last = items[items.length - 1];
        if (event.shiftKey && document.activeElement === first) { event.preventDefault(); last.focus(); }
        else if (!event.shiftKey && document.activeElement === last) { event.preventDefault(); first.focus(); }
      }
    });
    document.addEventListener("pointerdown", function (event) {
      if (document.body.classList.contains("mobile-nav-open") && !sidebar.contains(event.target) && !toggle.contains(event.target)) setOpen(false, false);
    });
    function update() { setOpen(false, false); }
    if (narrow.addEventListener) narrow.addEventListener("change", update);
    else narrow.addListener(update);
    update();
  }

  function initFilter() {
    var input = document.getElementById("result-filter");
    if (!input) return;
    var items = Array.prototype.slice.call(document.querySelectorAll("[data-filter-text]"));
    var count = document.getElementById("result-count");
    if (!count) {
      count = document.createElement("p");
      count.id = "result-count";
      count.className = "small muted";
      input.insertAdjacentElement("afterend", count);
    }
    count.setAttribute("role", "status");
    var description = input.getAttribute("aria-describedby") || "";
    if (description.split(" ").indexOf("result-count") < 0) input.setAttribute("aria-describedby", (description + " result-count").trim());
    var empty = document.getElementById("filter-empty");
    if (!empty) {
      empty = document.createElement("p");
      empty.id = "filter-empty";
      empty.className = "notice";
      empty.textContent = "No entries match this filter. Try a shorter name or another mathematical term.";
      empty.hidden = true;
      count.insertAdjacentElement("afterend", empty);
    }
    var prepared = items.map(function (node) { return { node: node, text: normalize(node.dataset.filterText) }; });
    function apply() {
      var terms = normalize(input.value).split(" ").filter(Boolean);
      var visible = 0;
      prepared.forEach(function (item) {
        var show = terms.every(function (term) { return item.text.indexOf(term) !== -1; });
        item.node.hidden = !show;
        if (show) visible += 1;
      });
      if (count) count.textContent = visible + " of " + items.length + " results";
      if (empty) empty.hidden = visible !== 0;
    }
    input.addEventListener("input", apply);
    apply();
  }

  function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      return navigator.clipboard.writeText(text).catch(function () { return fallbackCopy(text); });
    }
    return fallbackCopy(text);
  }
  function fallbackCopy(text) {
    var field = document.createElement("textarea");
    field.value = text;
    field.style.cssText = "position:fixed;left:-10000px;top:0;opacity:0";
    field.setAttribute("aria-label", "Text to copy");
    var active = document.activeElement;
    document.body.appendChild(field);
    field.select();
    var success = false;
    try { success = document.execCommand("copy"); } catch (_) { success = false; }
    field.remove();
    if (active && active.focus) active.focus({ preventScroll: true });
    return success ? Promise.resolve() : Promise.reject(new Error("Clipboard unavailable"));
  }
  function initCopy() {
    document.querySelectorAll("[data-copy-target]").forEach(function (button) {
      var initial = button.textContent;
      var timeout;
      button.addEventListener("click", function () {
        var selector = button.dataset.copyTarget;
        var target = document.getElementById(selector.replace(/^#/, ""));
        if (!target) { try { target = document.querySelector(selector); } catch (_) { target = null; } }
        if (!target) return;
        var lines = target.querySelectorAll(".line-code");
        var text = lines.length ? Array.prototype.map.call(lines, function (line) { return line.textContent; }).join("\n") : target.textContent;
        window.clearTimeout(timeout);
        copyText(text).then(function () { button.textContent = "Copied"; }, function () { button.textContent = "Select to copy"; })
          .then(function () { timeout = window.setTimeout(function () { button.textContent = initial; }, 2000); });
      });
    });
  }

  function initMath() {
    if (!window.katex || typeof window.katex.render !== "function") return;
    document.querySelectorAll("[data-tex]").forEach(function (element) {
      try {
        window.katex.render(element.dataset.tex, element, {
          displayMode: element.dataset.display === "true",
          output: "mathml", throwOnError: false, trust: false, strict: "ignore"
        });
      } catch (_) {
        element.textContent = element.dataset.tex;
        element.classList.add("katex-error");
      }
    });
  }

  function initToc() {
    if (!("IntersectionObserver" in window)) return;
    var links = Array.prototype.slice.call(document.querySelectorAll(".toc a[href^='#']"));
    var pairs = links.map(function (link) {
      var id;
      try { id = decodeURIComponent(link.getAttribute("href").slice(1)); } catch (_) { return null; }
      var target = document.getElementById(id);
      return target ? { link: link, target: target } : null;
    }).filter(Boolean);
    if (!pairs.length) return;
    function update() {
      var active = pairs[0];
      pairs.forEach(function (pair) { if (pair.target.getBoundingClientRect().top <= 145) active = pair; });
      pairs.forEach(function (pair) {
        var current = pair === active;
        pair.link.classList.toggle("active", current);
        if (current) pair.link.setAttribute("aria-current", "location");
        else pair.link.removeAttribute("aria-current");
      });
    }
    var observer = new IntersectionObserver(update, { rootMargin: "-90px 0px -65% 0px", threshold: [0, 1] });
    pairs.forEach(function (pair) { observer.observe(pair.target); });
    update();
  }

  ready(function () {
    var main = document.getElementById("main");
    var skip = document.querySelector(".skip-link");
    if (main && skip) {
      if (!main.hasAttribute("tabindex")) main.setAttribute("tabindex", "-1");
      skip.addEventListener("click", function () { main.focus({ preventScroll: true }); });
    }
    initSearch();
    initMobileNav();
    initFilter();
    initCopy();
    initMath();
    initToc();
  });
})();
