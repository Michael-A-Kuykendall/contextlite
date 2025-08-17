import { Server } from "@modelcontextprotocol/sdk/server";
import fetch from "node-fetch";

const BASE = process.env.CONTEXTLITE_URL || "http://localhost:8080";
const TOKEN = process.env.CONTEXTLITE_TOKEN || process.env.CONTEXTLITE_AUTH_TOKEN;

async function call(path: string, body: any) {
  const r = await fetch(`${BASE}${path}`, {
    method: "POST",
    headers: {
      "content-type": "application/json",
      ...(TOKEN ? { authorization: `Bearer ${TOKEN}` } : {}),
    },
    body: JSON.stringify(body),
  });
  if (!r.ok) throw new Error(`${path} ${r.status}`);
  return r.json();
}

const server = new Server({ name: "contextlite", version: "0.1.0" });

server.tool("search", { query: "string", k: { type: "number", optional: true } }, async ({ query, k }) => {
  const data = await call("/api/v1/rank", { query, k: k ?? 6, budget_ms: 80 });
  return data.items || [];
});

server.tool("fetch", { file: "string", start: { type: "object" }, end: { type: "object" } }, async (args) => {
  return await call("/api/v1/snippet", args);
});

server.start();
