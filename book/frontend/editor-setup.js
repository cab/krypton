/** Shared CodeMirror setup for Krypton editors (tour + REPL). */

import { EditorView } from "codemirror";
import kryptonTmLanguage from "../../vscode-grammar/krypton.tmLanguage.json";
import { createKryptonLanguage } from "./krypton-language.js";

export const kryptonLanguage = createKryptonLanguage(kryptonTmLanguage);

export const kryptonTheme = EditorView.theme({
  "&": {
    backgroundColor: "var(--code-bg)",
    color: "var(--code-fg)",
    fontFamily: "var(--mono)",
    fontSize: "14px",
    borderRadius: "0",
  },
  ".cm-content": {
    padding: "0.6rem 0",
    caretColor: "var(--code-fg)",
  },
  ".cm-scroller": {
    fontFamily: "var(--mono)",
    lineHeight: "1.5",
  },
  ".cm-line": {
    padding: "0 0.75rem",
  },
  ".cm-gutters": {
    backgroundColor: "var(--code-gutter-bg)",
    color: "var(--code-gutter-fg)",
    borderRight: "1px solid var(--code-gutter-border)",
    minWidth: "2.75rem",
  },
  ".cm-lineNumbers .cm-gutterElement": {
    padding: "0 0.65rem 0 0.85rem",
  },
  ".cm-activeLineGutter": {
    backgroundColor: "var(--code-active-line)",
    color: "var(--code-fg)",
  },
  ".cm-activeLine": {
    backgroundColor: "var(--code-active-line)",
  },
  "&.cm-focused": {
    outline: "none",
  },
  "&.cm-focused .cm-selectionBackground, ::selection": {
    backgroundColor: "var(--code-selection)",
  },
  ".cm-cursor, .cm-dropCursor": {
    borderLeftColor: "var(--accent)",
  },
  ".cm-keyword": {
    color: "var(--code-keyword)",
  },
  ".cm-operator": {
    color: "var(--code-operator)",
  },
  ".cm-number, .cm-bool": {
    color: "var(--code-number)",
  },
  ".cm-string": {
    color: "var(--code-string)",
  },
  ".cm-comment": {
    color: "var(--code-comment)",
    fontStyle: "italic",
  },
  ".cm-typeName": {
    color: "var(--code-type)",
  },
  ".cm-function, .cm-function-definition": {
    color: "var(--code-function)",
  },
  ".cm-variableName-special": {
    color: "var(--code-special)",
  },
});

export function renderDiagnosticsDom(diagnostics, container) {
  container.innerHTML = "";
  for (const diag of diagnostics) {
    const severity = diag.severity === "Error" ? "error" : "warning";
    const el = document.createElement("div");
    el.className = `diagnostic diagnostic-${severity}`;

    const header = document.createElement("div");
    header.className = "diag-header";

    const sevSpan = document.createElement("span");
    sevSpan.className = "diag-severity";
    sevSpan.textContent = severity;
    header.appendChild(sevSpan);

    if (diag.code) {
      const codeSpan = document.createElement("span");
      codeSpan.className = "diag-code";
      codeSpan.textContent = `[${diag.code}]`;
      header.appendChild(codeSpan);
    }

    header.appendChild(document.createTextNode(`: ${diag.message}`));
    el.appendChild(header);

    if (diag.primary_label) {
      const label = document.createElement("div");
      label.className = "diag-label";
      label.textContent = `  --> ${diag.primary_file}: ${diag.primary_label}`;
      el.appendChild(label);
    }

    for (const sec of diag.secondary_labels ?? []) {
      const label = document.createElement("div");
      label.className = "diag-label";
      label.textContent = `  --> ${sec.filename}: ${sec.message}`;
      el.appendChild(label);
    }

    if (diag.help) {
      const helpEl = document.createElement("div");
      helpEl.className = "diag-help";
      helpEl.textContent = `  help: ${diag.help}`;
      el.appendChild(helpEl);
    }

    if (diag.note) {
      const noteEl = document.createElement("div");
      noteEl.className = "diag-note";
      noteEl.textContent = `  note: ${diag.note}`;
      el.appendChild(noteEl);
    }

    container.appendChild(el);
  }
}
