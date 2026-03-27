import { basicSetup, EditorView } from "codemirror";
import { EditorState } from "@codemirror/state";
import { keymap } from "@codemirror/view";
import { indentUnit } from "@codemirror/language";

import kryptonTmLanguage from "../../vscode-grammar/krypton.tmLanguage.json";
import { createKryptonLanguage } from "./krypton-language.js";
import { runSnippet } from "./playground-client.js";

const kryptonLanguage = createKryptonLanguage(kryptonTmLanguage);

const kryptonTheme = EditorView.theme({
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

document.querySelectorAll(".code-block").forEach((block) => {
  const textarea = block.querySelector(".editor");
  const outputEl = block.querySelector(".output");
  const outputText = block.querySelector(".output-text");
  const runBtn = block.querySelector(".run-btn");

  if (!(textarea instanceof HTMLTextAreaElement)) {
    return;
  }

  const host = document.createElement("div");
  host.className = "editor-host";
  textarea.replaceWith(host);

  let view;
  const run = async () => {
    outputEl?.classList.add("visible");
    if (!outputText) {
      return;
    }
    outputText.textContent = "Running...";
    if (runBtn instanceof HTMLButtonElement) {
      runBtn.disabled = true;
    }
    try {
      const result = await runSnippet(view.state.doc.toString());
      outputText.textContent = result.output || "(no output)";
    } catch (error) {
      outputText.textContent =
        error instanceof Error ? `${error.name}: ${error.message}` : String(error);
    } finally {
      if (runBtn instanceof HTMLButtonElement) {
        runBtn.disabled = false;
      }
    }
  };

  view = new EditorView({
    parent: host,
    state: EditorState.create({
      doc: textarea.value,
      extensions: [
        basicSetup,
        EditorState.tabSize.of(2),
        indentUnit.of("  "),
        kryptonLanguage,
        kryptonTheme,
        keymap.of([
          {
            key: "Mod-Enter",
            run: () => {
              run();
              return true;
            },
          },
        ]),
      ],
    }),
  });

  runBtn?.addEventListener("click", run);
});
