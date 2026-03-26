import { basicSetup, EditorView } from "codemirror";
import { EditorState } from "@codemirror/state";
import { keymap } from "@codemirror/view";
import { indentUnit } from "@codemirror/language";

import kryptonTmLanguage from "../../vscode-grammar/krypton.tmLanguage.json";
import { createKryptonLanguage } from "./krypton-language.js";

const kryptonLanguage = createKryptonLanguage(kryptonTmLanguage);

const kryptonTheme = EditorView.theme({
  "&": {
    backgroundColor: "var(--code-bg)",
    color: "var(--fg)",
    fontFamily: "var(--mono)",
    fontSize: "14px",
  },
  ".cm-content": {
    padding: "0.5rem 0",
    caretColor: "var(--fg)",
  },
  ".cm-scroller": {
    fontFamily: "var(--mono)",
    lineHeight: "1.5",
  },
  ".cm-line": {
    padding: "0 0.75rem",
  },
  ".cm-gutters": {
    backgroundColor: "var(--code-bg)",
    color: "var(--muted)",
    borderRight: "1px solid var(--border)",
  },
  ".cm-activeLineGutter": {
    backgroundColor: "rgba(74, 108, 247, 0.08)",
  },
  ".cm-activeLine": {
    backgroundColor: "rgba(74, 108, 247, 0.05)",
  },
  "&.cm-focused": {
    outline: "none",
  },
  "&.cm-focused .cm-selectionBackground, ::selection": {
    backgroundColor: "rgba(74, 108, 247, 0.22)",
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
  const run = () => {
    outputEl?.classList.add("visible");
    outputText.textContent = "WASM compiler not yet loaded";
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
