import { basicSetup, EditorView } from "codemirror";
import { EditorState, Prec } from "@codemirror/state";
import { keymap } from "@codemirror/view";
import { indentUnit } from "@codemirror/language";
import { setDiagnostics, lintGutter } from "@codemirror/lint";

import { kryptonLanguage, kryptonTheme, renderDiagnosticsDom } from "./editor-setup.js";
import { runSnippet } from "./playground-client.js";

function toCmDiagnostics(diagnostics) {
  return diagnostics
    .filter((d) => d.primary_span)
    .map((d) => ({
      from: d.primary_span[0],
      to: d.primary_span[1],
      severity: d.severity === "Error" ? "error" : "warning",
      message: d.message,
      source: d.code,
    }));
}

function createEditorState(doc, { readOnly = false, onRun } = {}) {
  const extensions = [
    basicSetup,
    EditorState.tabSize.of(2),
    indentUnit.of("  "),
    kryptonLanguage,
    kryptonTheme,
  ];

  if (readOnly) {
    extensions.push(EditorState.readOnly.of(true));
    extensions.push(EditorView.editable.of(false));
  } else {
    extensions.push(lintGutter());
    extensions.push(
      Prec.highest(
        keymap.of([
          {
            key: "Mod-Enter",
            run: () => {
              onRun?.();
              return true;
            },
          },
        ]),
      ),
    );
  }

  return EditorState.create({
    doc,
    extensions,
  });
}

document.querySelectorAll(".code-block").forEach((block) => {
  const mode = block.dataset.codeMode ?? "runnable";
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

  let view = null;
  if (mode === "static") {
    view = new EditorView({
      parent: host,
      state: createEditorState(textarea.value, { readOnly: true }),
    });
    return;
  }

  let isRunning = false;
  const run = async () => {
    if (!outputText || isRunning) {
      return;
    }

    const spinnerFrames = ["/", "-", "\\", "|"];
    let spinnerIndex = 0;
    const renderSpinner = () => {
      outputText.textContent = spinnerFrames[spinnerIndex];
      spinnerIndex = (spinnerIndex + 1) % spinnerFrames.length;
    };
    const spinnerTimer = window.setInterval(renderSpinner, 120);
    const stopSpinner = () => {
      window.clearInterval(spinnerTimer);
    };

    isRunning = true;
    outputEl?.classList.add("visible");
    renderSpinner();
    if (runBtn instanceof HTMLButtonElement) {
      runBtn.disabled = true;
    }
    try {
      const result = await runSnippet(view.state.doc.toString(), (log) => {
        stopSpinner();
        outputText.textContent = log;
        outputText.scrollTop = outputText.scrollHeight;
      });
      const diagnostics = result.diagnostics ?? [];
      if (diagnostics.length > 0) {
        stopSpinner();
        renderDiagnosticsDom(diagnostics, outputText);
        view.dispatch(setDiagnostics(view.state, toCmDiagnostics(diagnostics)));
      } else {
        stopSpinner();
        outputText.textContent = result.output || "(no output)";
        requestAnimationFrame(() => {
          outputText.scrollTop = outputText.scrollHeight;
        });
        view.dispatch(setDiagnostics(view.state, []));
      }
    } catch (error) {
      stopSpinner();
      outputText.textContent =
        error instanceof Error
          ? `${error.name}: ${error.message}`
          : String(error);
      view.dispatch(setDiagnostics(view.state, []));
    } finally {
      stopSpinner();
      isRunning = false;
      if (runBtn instanceof HTMLButtonElement) {
        runBtn.disabled = false;
      }
    }
  };

  view = new EditorView({
    parent: host,
    state: createEditorState(textarea.value, { onRun: run }),
  });

  runBtn?.addEventListener("click", run);
});
