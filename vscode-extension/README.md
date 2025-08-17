# ContextLite VS Code Extension

> **SMT-optimized context assembly for AI coding assistants**

## 🚀 Quick Setup for Sales

### 1. Install Dependencies

```bash
cd vscode-extension
npm install
```

### 2. Copy Binaries

Build the Go binaries and copy them to the `bin/` directory:

```bash
# From the main contextlite directory
make build-all

# Copy binaries to extension
cp build/contextlite vscode-extension/bin/contextlite-linux
cp build/contextlite.exe vscode-extension/bin/contextlite.exe  # Windows
# For Mac: GOOS=darwin GOARCH=amd64 go build -o vscode-extension/bin/contextlite-mac ./cmd/contextlite
```

### 3. Set Up Stripe Payment Link

1. Go to [stripe.com](https://stripe.com) and create account
2. Create product: "ContextLite Commercial License" - $99
3. Get payment link (format: `https://buy.stripe.com/abc123`)
4. Update the link in `src/extension.ts` (search for `YOUR-STRIPE-LINK-HERE`)

### 4. Package Extension

```bash
npm install -g vsce
vsce package
```

This creates `contextlite-1.0.0.vsix`

### 5. Publish Extension

```bash
# First time: create publisher
vsce create-publisher your-username

# Publish
vsce publish
```

## 💰 Sales Process

### Customer Journey:
1. **Download** → 14-day free trial starts
2. **Trial expires** → Extension shows "Buy License" button  
3. **Customer clicks** → Goes to your Stripe payment link
4. **Customer pays $99** → Stripe emails them receipt
5. **You email license key** → `CL-2024-ABC123XYZ` (manual process)
6. **Customer enters key** → Extension unlocked forever

### Manual License Email Template:

```
Subject: Your ContextLite Commercial License

Hi [Customer Name],

Thanks for purchasing ContextLite! 

Your license key: CL-2024-ABC123XYZ789

To activate:
1. Open VS Code  
2. Press Ctrl+, (settings)
3. Search "contextlite"
4. Paste your key in "License Key" field

Questions? Just reply to this email.

Thanks!
[Your name]
```

### Revenue Expectations:
- 100 downloads → 10% convert → $990 revenue
- 1,000 downloads → 10% convert → $9,900 revenue  
- 10,000 downloads → 5% convert → $49,500 revenue

## 🔧 Extension Features

- **Add to Context**: Right-click selection → Add to ContextLite database
- **Assemble Context**: Command palette → Query for optimal document set
- **Clear Context**: Reset the database
- **License Management**: Trial tracking + license key validation

## 📦 What's Included

- ✅ 14-day trial with automatic expiration
- ✅ License key validation (`CL-2024-` prefix)
- ✅ Stripe payment integration (manual fulfillment)
- ✅ VS Code commands + right-click menus
- ✅ ContextLite server management
- ✅ Real-time feedback with timing metrics
- ✅ Professional packaging for marketplace

## 🎯 Next Steps

1. **Set up Stripe** (15 minutes)
2. **Update payment link** in extension.ts
3. **Build & package** extension
4. **Submit to marketplace** 
5. **Start getting customers**

**You could be making money this weekend!**

---

*No servers to maintain, no complex licensing systems, just extension → Stripe → manual email → profit.*
