import path from "node:path";
import { fileURLToPath } from "node:url";
import { nodeResolve } from "../.lake/packages/proofwidgets/widget/node_modules/@rollup/plugin-node-resolve/dist/es/index.js";
import commonjs from "../.lake/packages/proofwidgets/widget/node_modules/@rollup/plugin-commonjs/dist/es/index.js";
import replace from "../.lake/packages/proofwidgets/widget/node_modules/@rollup/plugin-replace/dist/es/index.js";
import terser from "../.lake/packages/proofwidgets/widget/node_modules/@rollup/plugin-terser/dist/es/index.js";

const root = fileURLToPath(new URL("..", import.meta.url));
const proofwidgetsNodeModules = path.join(root, ".lake", "packages", "proofwidgets", "widget", "node_modules");
const htmlDisplayPath = path.join(root, ".lake", "packages", "proofwidgets", ".lake", "build", "js", "htmlDisplay.js");
const penroseDisplayPath = path.join(root, ".lake", "packages", "proofwidgets", ".lake", "build", "js", "penroseDisplay.js");
const shimPath = path.join(root, "CoherenceTactics", "Assets", "infoview-shim.js");
const reactPath = path.join(proofwidgetsNodeModules, "react", "index.js");
const reactJsxRuntimePath = path.join(proofwidgetsNodeModules, "react", "jsx-runtime.js");
const reactDomClientPath = path.join(proofwidgetsNodeModules, "react-dom", "client.js");
const reactDomPath = path.join(proofwidgetsNodeModules, "react-dom", "index.js");
const inputPath = path.join(root, "CoherenceTactics", "Assets", "string-diagram-host.js");
const outputPath = path.join(root, "CoherenceTactics", "Assets", "string-diagram-widget.js");

function localResolver() {
  return {
    name: "string-diagram-local-resolver",
    resolveId(source) {
      if (source === "proofwidgets-html-display") return htmlDisplayPath;
      if (source === "proofwidgets-penrose-display") return penroseDisplayPath;
      if (source === "proofwidgets-infoview-shim") return shimPath;
      if (source === "@leanprover/infoview") return shimPath;
      if (source === "react") return reactPath;
      if (source === "react/jsx-runtime") return reactJsxRuntimePath;
      if (source === "react-dom/client") return reactDomClientPath;
      if (source === "react-dom") return reactDomPath;
      return null;
    },
  };
}

export default {
  input: inputPath,
  output: {
    file: outputPath,
    format: "es",
    intro: "const global = window;",
    sourcemap: false,
    compact: true,
  },
  plugins: [
    localResolver(),
    nodeResolve({
      browser: true,
    }),
    replace({
      "typeof window": JSON.stringify("object"),
      "process.env.NODE_ENV": JSON.stringify("production"),
      preventAssignment: true,
    }),
    commonjs({
      ignore: [
        "process", "events", "stream", "util", "path", "buffer", "querystring", "url",
        "string_decoder", "punycode", "http", "https", "os", "assert", "constants",
        "timers", "console", "vm", "zlib", "tty", "domain", "dns", "dgram", "child_process",
        "cluster", "module", "net", "readline", "repl", "tls", "fs", "crypto", "perf_hooks",
      ],
    }),
    terser(),
  ],
};
