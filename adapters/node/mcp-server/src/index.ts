import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { 
  CallToolRequestSchema,
  ListToolsRequestSchema
} from "@modelcontextprotocol/sdk/types.js";
import fetch from "node-fetch";

const BASE = process.env.CONTEXTLITE_URL || "http://localhost:8084";
const TOKEN = process.env.CONTEXTLITE_TOKEN || "contextlite-dev-token-2025";

async function call(path: string, body?: any, method: string = "POST") {
  const options: any = {
    method,
    headers: {
      "content-type": "application/json",
      "Authorization": `Bearer ${TOKEN}`,
    },
  };
  
  if (body && method !== "GET") {
    options.body = JSON.stringify(body);
  } else if (method === "GET" && body) {
    // For GET requests, convert body to query parameters
    const params = new URLSearchParams(body);
    path += "?" + params.toString();
  }
  
  const r = await fetch(`${BASE}${path}`, options);
  if (!r.ok) throw new Error(`${path} ${r.status}: ${await r.text()}`);
  return r.json();
}

const server = new Server(
  {
    name: "contextlite",
    version: "1.0.0"
  },
  {
    capabilities: {
      tools: {}
    }
  }
);

server.setRequestHandler(ListToolsRequestSchema, async () => {
  return {
    tools: [
      {
        name: "assemble_context",
        description: "Assemble context using ContextLite's optimization engine",
        inputSchema: {
          type: "object",
          properties: {
            query: {
              type: "string",
              description: "Query to assemble context for"
            },
            max_tokens: {
              type: "number",
              description: "Maximum tokens to return",
              default: 4000
            },
            max_documents: {
              type: "number", 
              description: "Maximum documents to include",
              default: 8
            }
          },
          required: ["query"]
        }
      },
      {
        name: "search_documents",
        description: "Search documents in the ContextLite index",
        inputSchema: {
          type: "object",
          properties: {
            query: {
              type: "string",
              description: "Search query"
            },
            limit: {
              type: "number",
              description: "Maximum results to return",
              default: 10
            }
          },
          required: ["query"]
        }
      },
      {
        name: "get_storage_info",
        description: "Get information about the ContextLite storage system",
        inputSchema: {
          type: "object",
          properties: {}
        }
      }
    ]
  };
});

server.setRequestHandler(CallToolRequestSchema, async (request: any) => {
  const { name, arguments: args } = request.params;
  
  if (!args) {
    throw new Error("Missing arguments");
  }
  
  try {
    let result;
    
    switch (name) {
      case "assemble_context":
        result = await call("/api/v1/context/assemble", {
          query: args.query,
          max_tokens: args.max_tokens || 4000,
          max_documents: args.max_documents || 8
        });
        break;
        
      case "search_documents":
        result = await call("/api/v1/documents/search", {
          q: args.query,
          limit: args.limit || 10
        }, "GET");
        break;
        
      case "get_storage_info":
        result = await call("/api/v1/storage/info", {}, "GET");
        break;
        
      default:
        throw new Error(`Unknown tool: ${name}`);
    }
    
    return {
      content: [
        {
          type: "text",
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  } catch (error) {
    return {
      content: [
        {
          type: "text", 
          text: `Error: ${error instanceof Error ? error.message : String(error)}`
        }
      ],
      isError: true
    };
  }
});

const transport = new StdioServerTransport();
await server.connect(transport);
