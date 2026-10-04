/* Offline dependency-map enhancement. The complete diagram and links are static HTML. */
(function () {
  "use strict";

  function ready(fn) {
    if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", fn, { once: true });
    else fn();
  }

  ready(function () {
    var root = document.getElementById("dependency-map");
    if (!root || root.classList.contains("dependency-enhanced")) return;
    var buttons = Array.prototype.slice.call(root.querySelectorAll(".dependency-selector[data-stage]"));
    var nodes = Array.prototype.slice.call(root.querySelectorAll(".dependency-node[data-stage]"));
    var details = Array.prototype.slice.call(root.querySelectorAll(".dependency-detail[data-stage]"));
    var edges = Array.prototype.slice.call(root.querySelectorAll(".dependency-edge[data-from][data-to]"));
    var reset = root.querySelector("#dependency-reset");
    var status = root.querySelector("#dependency-status");
    var stages = Object.create(null);
    var selected = "";

    // Incomplete markup keeps its readable, unfiltered fallback.
    if (!buttons.length || buttons.length !== nodes.length || buttons.length !== details.length || !reset || !status) return;
    var valid = buttons.every(function (button) {
      var id = button.dataset.stage;
      if (!/^[a-z0-9][a-z0-9-]*$/.test(id) || stages[id]) return false;
      stages[id] = { label: button.textContent.replace(/\s+/g, " ").trim(), button: button };
      return true;
    });
    valid = details.every(function (detail) {
      var stage = stages[detail.dataset.stage];
      if (!stage || stage.detail || detail.id !== "stage-" + detail.dataset.stage) return false;
      stage.detail = detail;
      return true;
    }) && valid;
    valid = nodes.every(function (node) {
      var stage = stages[node.dataset.stage];
      if (!stage || stage.node) return false;
      stage.node = node;
      return true;
    }) && valid;
    valid = edges.every(function (edge) {
      return stages[edge.dataset.from] && stages[edge.dataset.to] &&
        edge.dataset.from !== edge.dataset.to && /^(ingredient|comparison)$/.test(edge.dataset.kind);
    }) && valid;
    if (!valid) return;

    root.classList.add("dependency-enhanced");
    status.setAttribute("role", "status");
    status.setAttribute("aria-live", "polite");
    status.setAttribute("aria-atomic", "true");
    buttons.forEach(function (button) {
      button.setAttribute("aria-controls", stages[button.dataset.stage].detail.id);
      button.setAttribute("aria-pressed", "false");
    });
    details.forEach(function (detail) {
      if (!detail.hasAttribute("tabindex")) detail.setAttribute("tabindex", "-1");
    });

    function hashStage() {
      var hash;
      try { hash = decodeURIComponent(window.location.hash); } catch (_) { return ""; }
      var id = hash.indexOf("#stage-") === 0 ? hash.slice(7) : "";
      return stages[id] ? id : "";
    }

    function updateHash(id) {
      var url = new URL(window.location.href);
      if (id) url.hash = "stage-" + id;
      else if (hashStage()) url.hash = "";
      try { window.history.replaceState(window.history.state, "", url.href); } catch (_) {
        // Some local-file browsers restrict history changes; selection still works.
      }
    }

    function labels(ids) {
      return buttons.filter(function (button) { return ids[button.dataset.stage]; })
        .map(function (button) { return stages[button.dataset.stage].label; }).join(", ") || "none";
    }

    function select(id, changeHash) {
      selected = stages[id] ? id : "";
      var prerequisites = Object.create(null);
      var dependents = Object.create(null);
      var comparisons = Object.create(null);
      edges.forEach(function (edge) {
        var from = edge.dataset.from, to = edge.dataset.to;
        var incident = selected && (from === selected || to === selected);
        if (incident && edge.dataset.kind === "comparison") comparisons[from === selected ? to : from] = true;
        else if (incident) {
          if (to === selected) prerequisites[from] = true;
          if (from === selected) dependents[to] = true;
        }
        edge.classList.toggle("dependency-active-edge", Boolean(incident));
        edge.classList.toggle("dependency-muted", Boolean(selected && !incident));
      });
      nodes.forEach(function (node) {
        var stage = node.dataset.stage;
        var chosen = stage === selected;
        node.classList.toggle("dependency-selected", chosen);
        node.classList.toggle("dependency-prerequisite", Boolean(prerequisites[stage]));
        node.classList.toggle("dependency-dependent", Boolean(dependents[stage]));
        node.classList.toggle("dependency-comparison-neighbor", Boolean(comparisons[stage]));
        node.classList.toggle("dependency-muted", Boolean(selected && !chosen &&
          !prerequisites[stage] && !dependents[stage] && !comparisons[stage]));
        var link = node.querySelector("a");
        if (link) {
          if (chosen) link.setAttribute("aria-current", "location");
          else link.removeAttribute("aria-current");
        }
      });
      buttons.forEach(function (button) {
        button.setAttribute("aria-pressed", String(button.dataset.stage === selected));
      });
      details.forEach(function (detail) { detail.hidden = Boolean(selected && detail.dataset.stage !== selected); });
      if (selected) {
        root.dataset.selected = selected;
        status.textContent = "Selected: " + stages[selected].label + ". Direct prerequisites: " + labels(prerequisites) +
          ". Direct dependents: " + labels(dependents) + ". Comparison links: " + labels(comparisons) + ".";
      } else {
        delete root.dataset.selected;
        status.textContent = "All " + buttons.length + " proof stages shown. Solid arrows run from prerequisite to consumer; dotted links mark comparisons.";
      }
      if (changeHash) updateHash(selected);
    }

    root.addEventListener("click", function (event) {
      if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
      var target = event.target.closest && event.target.closest(".dependency-selector, a[href^='#stage-']");
      if (!target || !root.contains(target)) return;
      var id = target.dataset.stage;
      var isLink = target.tagName.toLowerCase() === "a";
      if (isLink) {
        try { id = decodeURIComponent(target.getAttribute("href").slice(7)); } catch (_) { return; }
      }
      if (!stages[id]) return;
      event.preventDefault();
      select(id, true);
      if (isLink) {
        stages[id].detail.focus({ preventScroll: true });
        stages[id].detail.scrollIntoView({ block: "start", behavior: "auto" });
      }
    });
    reset.addEventListener("click", function () { select("", true); });
    root.addEventListener("keydown", function (event) {
      if (event.key === "Escape" && selected) {
        event.preventDefault();
        select("", true);
      }
    });
    window.addEventListener("hashchange", function () { select(hashStage(), false); });
    select(hashStage() || root.dataset.defaultStage || "", false);
  });
})();
