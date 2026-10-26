// Lean names in table cells may break only after "." and "_", never inside a word
// (extra.css turns off Material's break-anywhere for table code). Material's instant
// navigation replaces the page content without a reload, so this runs on every page view.
(function () {
  function leanNameBreaks() {
    document.querySelectorAll(".md-typeset td code, .md-typeset th code").forEach(function (code) {
      if (code.dataset.leanBreaks || code.children.length) return;
      code.dataset.leanBreaks = "1";
      var parts = code.textContent.replace(/([._])/g, "$1\u0000").split("\u0000");
      if (parts.length < 2) return;
      code.textContent = "";
      parts.forEach(function (part, i) {
        if (i) code.appendChild(document.createElement("wbr"));
        code.appendChild(document.createTextNode(part));
      });
    });
  }
  if (typeof document$ !== "undefined") document$.subscribe(leanNameBreaks);
  else document.addEventListener("DOMContentLoaded", leanNameBreaks);
})();
