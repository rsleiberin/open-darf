# Darf-Tech Frontend

Welcome to the **Darf-Tech Frontend** project! This repository is designed to be a **scalable, modern** frontend solution using **Next.js v15.1.6**, **React v19**, **Tailwind CSS v4**, and **shadcn/UI** for component management.

We follow **best practices for UI, accessibility, performance, and developer experience** with a well-structured approach to testing, CI/CD, and automation.

---

## 🚀 Overview

### **Tech Stack**

- **Next.js 15+** (App Router inside `src/app`)
- **React 19+** (Concurrent Mode, RSC support)
- **Tailwind CSS 4+** (Utility-first styling, contrast-aware themes)
- **shadcn/UI** (Composable UI components)
- **TypeScript** (Static typing and safety)
- **ESLint & Prettier** (Code quality enforcement)
- **Jest & Vitest** (Unit & component testing)
- **Husky & Lint-Staged** (Pre-commit and pre-push validation)
- **GitHub Actions** (Automated CI/CD workflows)

---

## 📚 Directory Structure

```
frontend/
├─ .github/workflows/       (CI/CD automation)
├─ .husky/                  (Git hooks for linting & testing)
├─ archive/                 (Legacy documentation & references)
├─ components.json          (shadcn UI config for component generation)
├─ dist/                    (Compiled Tailwind artifacts via CLI)
├─ public/                  (Static assets, SVGs, fonts)
├─ src/
├── README.md                            # Documentation
│
├── archive/                             # Research and documentation archive
│   ├── README.md
│                                        # Index for archived research
├─ tailwind.config.js       (Tailwind setup, theme customization)
├─ tsconfig.json            (TypeScript configuration)
├─ jest.config.ts           (Jest configuration for unit testing)
├─ jest.setup.ts            (Jest setup file for test environment)
├─ package.json             (Project dependencies & scripts)
└─ README.md                (This file)
```

### 📖 **Documentation Plan**
Each key directory should contain **its own README.md** to explain its purpose:
- `src/components/ui/README.md`: shadcn UI component customization & best practices.
- `src/app/ui-preview/README.md`: Usage guide for previewing components.
- `src/lib/README.md`: Explanation of reusable utilities.
- `__tests__/README.md`: How to write and structure tests.

---

## 🏠 Getting Started

### **1️⃣ Installation**

```sh
npm install
```

### **2️⃣ Development Mode**

```sh
npm run dev
```
- The app will run on **`localhost:3000`** (or next available port).

### **3️⃣ Production Build**

```sh
npm run build
npm run start
```
- Generates an optimized build for deployment.

---

## 🧙‍♂️ shadcn/UI Integration

**shadcn/UI** provides flexible, composable components. To generate a new component:

```sh
npx shadcn add button
```

### **Best Practices:**
- All components are stored in **`src/components/ui/`**.
- Customize via `tailwind.config.js` and `globals.css`.
- Uses Tailwind tokens (`hsl(var(--background))`) for consistent theming.
- Supports **dark mode** out of the box.

🔗 **Reference:** [shadcn UI Docs](https://ui.shadcn.com)

---

## 🎨 Tailwind CSS 4+ Theming

### **Key Features in Tailwind 4:**
- **Contrast-Based Theming:** Dynamic `hsl(var(--background))` colors.
- **Optimized `@apply` Usage:** Improved utility class composition.
- **Built-in Performance Optimizations:** Automatic tree-shaking.

#### **Example: Custom Theme (Defined in `globals.css`)**

```css
@layer base {
  :root {
    --background: 0 0% 100%;
  }
  .dark {
    --background: 222 84% 4.9%;
  }
}

@layer utilities {
  .bg-background {
    background-color: hsl(var(--background));
  }
}
```

---

## 🧑‍🔧 Testing Setup

We use **Jest** & **Vitest** for unit and component testing.

```sh
npm test
```

### **Planned Test Coverage:**
🗳 UI snapshots (shadcn components)  
🗳 Unit tests (`lib/utils.ts`)  
🗳 Integration tests (User interactions)

#### **Enable Code Coverage Reports**
Modify `jest.config.ts`:
```ts
export default {
  preset: "ts-jest",
  testEnvironment: "jsdom",
  collectCoverage: true,
  coverageDirectory: "coverage",
};
```
Run tests with coverage:
```sh
npm test -- --coverage
```

---

## ⚡ Automation & CI/CD

### **Pre-Commit & Pre-Push Hooks**
- **Husky:** Ensures linting & tests **before pushing**.
- **Lint-Staged:** Runs only on staged files to speed up validation.

#### **Manual Trigger**
```sh
npm run precheck
```

### **GitHub Actions CI/CD**
- Every push triggers:
  - **ESLint & Prettier validation**
  - **Jest tests**

---

## 📌 Atomic Design & Component Architecture

We are reviewing whether to fully adopt **Atomic Design** alongside **shadcn/UI**.

👉 **Current Approach:**
- **shadcn UI** in `components/ui/`
- **Core utilities** in `lib/utils.ts`
- **Potential** full atomic structure in future

📚 _See `archive/` for older atomic design research._

---

## 🤮 Future Enhancements

1. **Expand shadcn/UI components & theming**
2. **Refine Tailwind contrast-based theming**
3. **Enhance Jest/Vitest test coverage**
4. **Decide on final Atomic vs. Standard component organization**
5. **Performance optimizations (e.g. Framer Motion for animations)**

---

## 🤝 Contributing

1. **Branch from `main`** for new features.
2. **Ensure tests & linting pass** before PRs.
3. **Submit PRs with screenshots (for UI changes).**
4. **Merge after review.**

---

## 🐟 License

_(TBD—specify open-source or proprietary licensing here.)_

---

Thank you for contributing to **Darf-Tech Frontend**! This project is designed for **scalability, automation, and developer experience**. As we refine our architecture, this README will evolve to reflect best practices. 🚀

