import { StreamLanguage } from "@codemirror/language";

function anchored(source) {
  return new RegExp(`^(?:${source})`);
}

function tokenPattern(name, repository) {
  return anchored(repository[name].match);
}

function tokenPatterns(name, repository) {
  return repository[name].patterns.map((pattern) => anchored(pattern.match));
}

function consumeString(stream, state) {
  let escaped = false;

  while (!stream.eol()) {
    const ch = stream.next();
    if (escaped) {
      escaped = false;
      continue;
    }
    if (ch === "\\") {
      escaped = true;
      continue;
    }
    if (ch === "\"") {
      state.inString = false;
      return "string";
    }
  }

  state.inString = true;
  return "string";
}

export function createKryptonLanguage(tmLanguage) {
  const repository = tmLanguage.repository;
  const comment = tokenPattern("comment", repository);
  const number = tokenPattern("number", repository);
  const constant = tokenPattern("constant", repository);
  const keywordControl = tokenPattern("keyword-control", repository);
  const keywordDeclaration = tokenPattern("keyword-declaration", repository);
  const operatorOwnership = tokenPattern("operator-ownership", repository);
  const multiOperators = tokenPatterns("operator-multi", repository);
  const singleOperators = tokenPatterns("operator-single", repository);
  const typeName = tokenPattern("type-name", repository);
  const wildcard = tokenPattern("wildcard", repository);
  const functionName = anchored("[a-z_][a-zA-Z0-9_]*");

  return StreamLanguage.define({
    name: "krypton",
    startState() {
      return {
        inString: false,
        expectFunctionName: false,
      };
    },
    copyState(state) {
      return { ...state };
    },
    token(stream, state) {
      if (stream.eatSpace()) {
        return null;
      }

      if (state.inString) {
        return consumeString(stream, state);
      }

      if (stream.match(comment)) {
        state.expectFunctionName = false;
        return "comment";
      }

      if (stream.peek() === "\"") {
        stream.next();
        state.expectFunctionName = false;
        state.inString = true;
        return consumeString(stream, state);
      }

      if (state.expectFunctionName) {
        const match = stream.match(functionName);
        if (match) {
          state.expectFunctionName = false;
          return "function.definition";
        }
        state.expectFunctionName = false;
      }

      if (stream.match(number)) {
        return "number";
      }

      if (stream.match(constant)) {
        return "bool";
      }

      if (stream.match(keywordControl)) {
        return "keyword";
      }

      const declaration = stream.match(keywordDeclaration);
      if (declaration) {
        state.expectFunctionName = declaration[0] === "fun";
        return "keyword";
      }

      if (stream.match(operatorOwnership)) {
        return "operator";
      }

      for (const operator of multiOperators) {
        if (stream.match(operator)) {
          return "operator";
        }
      }

      for (const operator of singleOperators) {
        if (stream.match(operator)) {
          return "operator";
        }
      }

      if (stream.match(typeName)) {
        return "typeName";
      }

      if (stream.match(wildcard)) {
        return "variableName.special";
      }

      stream.next();
      return null;
    },
    languageData: {
      commentTokens: { line: "#" },
      closeBrackets: { brackets: ["(", "[", "{", "\""] },
      indentOnInput: /^\s*[\]}]$/,
    },
  });
}
