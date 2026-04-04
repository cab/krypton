import { EditorView, minimalSetup } from "codemirror";
import { EditorState, Prec } from "@codemirror/state";
import { keymap } from "@codemirror/view";
import { indentUnit } from "@codemirror/language";
import { closeBrackets } from "@codemirror/autocomplete";

import { kryptonLanguage, kryptonTheme, renderDiagnosticsDom } from "./editor-setup.js";
import { createReplClient } from "./repl-client.js";

const client = createReplClient();
const output = document.querySelector(".repl-output");
const inputArea = document.querySelector(".repl-input-area");
const promptSpan = document.querySelector(".repl-prompt");
const editorHost = document.querySelector(".repl-editor");

// History
const history = [];
let historyIndex = -1;
let savedInput = "";

// Bracket depth tracking for multi-line
function bracketDepth(text) {
  let depth = 0;
  for (const ch of text) {
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    if (ch === ")" || ch === "]" || ch === "}") depth--;
  }
  return depth;
}

function isBalanced(text) {
  return bracketDepth(text) <= 0;
}

const replTheme = EditorView.theme({
  "&": {
    backgroundColor: "transparent",
    color: "var(--code-fg)",
    fontFamily: "var(--mono)",
    fontSize: "14px",
  },
  ".cm-content": {
    padding: "0",
    caretColor: "var(--code-fg)",
  },
  ".cm-scroller": {
    fontFamily: "var(--mono)",
    lineHeight: "1.5",
    overflow: "visible",
  },
  ".cm-line": {
    padding: "0",
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
});

let isRunning = false;

async function submit() {
  const text = view.state.doc.toString();
  if (!text.trim()) return;
  if (!isBalanced(text)) return; // keep editing multi-line

  if (isRunning) return;
  isRunning = true;

  // Save to history
  if (history[history.length - 1] !== text) {
    history.push(text);
  }
  historyIndex = -1;
  savedInput = "";

  // Echo input
  const entry = document.createElement("div");
  entry.className = "repl-entry";

  const echo = document.createElement("pre");
  echo.className = "repl-echo";
  const lines = text.split("\n");
  echo.textContent = lines
    .map((line, i) => (i === 0 ? `> ${line}` : `.. ${line}`))
    .join("\n");
  entry.appendChild(echo);

  const resultEl = document.createElement("pre");
  resultEl.className = "repl-result";
  entry.appendChild(resultEl);
  output.appendChild(entry);

  // Clear editor
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: "" },
  });
  promptSpan.textContent = "> ";

  // Handle commands
  const trimmed = text.trim();
  if (trimmed === ":reset") {
    client.reset();
    output.innerHTML = "";
    appendBanner();
    isRunning = false;
    scrollToBottom();
    return;
  }
  if (trimmed === ":help") {
    resultEl.textContent =
      "Commands:\n  :reset  Clear all state\n  :help   Show this message";
    isRunning = false;
    scrollToBottom();
    return;
  }

  try {
    const result = await client.eval(trimmed, (log) => {
      resultEl.textContent = log;
      scrollToBottom();
    });

    const diagnostics = result.diagnostics ?? [];
    if (diagnostics.length > 0) {
      renderDiagnosticsDom(diagnostics, resultEl);
    } else if (result.output) {
      resultEl.textContent = result.output;
      if (!result.ok) {
        resultEl.classList.add("repl-error");
      }
    } else if (!result.ok) {
      resultEl.textContent = result.output || "Error";
      resultEl.classList.add("repl-error");
    }
  } catch (error) {
    resultEl.textContent =
      error instanceof Error ? `${error.name}: ${error.message}` : String(error);
    resultEl.classList.add("repl-error");
  } finally {
    isRunning = false;
    scrollToBottom();
    view.focus();
  }
}

function scrollToBottom() {
  requestAnimationFrame(() => {
    output.scrollTop = output.scrollHeight;
  });
}

function appendBanner() {
  const banner = document.createElement("div");
  banner.className = "repl-banner";
  banner.textContent = "Krypton v0.1 — Type :help for commands.";
  output.appendChild(banner);
}

function navigateHistory(direction) {
  if (history.length === 0) return false;

  if (historyIndex === -1) {
    savedInput = view.state.doc.toString();
  }

  if (direction === "up") {
    if (historyIndex === -1) {
      historyIndex = history.length - 1;
    } else if (historyIndex > 0) {
      historyIndex--;
    } else {
      return false;
    }
  } else {
    if (historyIndex === -1) return false;
    if (historyIndex < history.length - 1) {
      historyIndex++;
    } else {
      historyIndex = -1;
    }
  }

  const text = historyIndex === -1 ? savedInput : history[historyIndex];
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: text },
    selection: { anchor: text.length },
  });
  return true;
}

const replKeymap = keymap.of([
  {
    key: "Enter",
    run: (view) => {
      const text = view.state.doc.toString();
      if (isBalanced(text)) {
        submit();
        return true;
      }
      // Unbalanced — insert newline
      return false;
    },
  },
  {
    key: "Shift-Enter",
    run: () => false, // let default newline through
  },
  {
    key: "ArrowUp",
    run: (view) => {
      const cursor = view.state.selection.main;
      const firstLine = view.state.doc.lineAt(cursor.head);
      if (firstLine.number === 1) {
        return navigateHistory("up");
      }
      return false;
    },
  },
  {
    key: "ArrowDown",
    run: (view) => {
      const cursor = view.state.selection.main;
      const lastLine = view.state.doc.lineAt(cursor.head);
      if (lastLine.number === view.state.doc.lines) {
        return navigateHistory("down");
      }
      return false;
    },
  },
]);

// Update prompt for multi-line
const promptUpdater = EditorView.updateListener.of((update) => {
  if (update.docChanged) {
    const text = update.state.doc.toString();
    promptSpan.textContent = text.includes("\n") || !isBalanced(text) ? ".. " : "> ";
  }
});

const view = new EditorView({
  parent: editorHost,
  state: EditorState.create({
    doc: "",
    extensions: [
      minimalSetup,
      EditorState.tabSize.of(2),
      indentUnit.of("  "),
      closeBrackets(),
      kryptonLanguage,
      kryptonTheme,
      replTheme,
      Prec.highest(replKeymap),
      promptUpdater,
    ],
  }),
});

appendBanner();
view.focus();
