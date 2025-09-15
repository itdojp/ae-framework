# Inventory Management Example

> 🌍 Language / 言語: English | 日本語

> **Phase 3→5→6 エンドツーエンド・デモ**  
> 要求→モデル→UI→CI→承認の完全自動化フローを体験

## 🎯 Overview

この例題は、ae-frameworkの**Phase 3-6**の統合デモンストレーションです：

1. **Phase 3**: ユーザーストーリー作成
2. **Phase 5**: ドメインモデリング  
3. **Phase 6**: UI自動生成 + Quality Gates

## 📋 User Stories

### Epic: 在庫管理システム

**AS A** store manager  
**I WANT TO** manage product inventory efficiently  
**SO THAT** I can track stock levels and optimize sales

#### Story 1: Product Management
- **AS A** store manager
- **I WANT TO** add, edit, and view products
- **SO THAT** I can maintain accurate product catalog

**Acceptance Criteria:**
- [ ] Can create new product with name, description, price, stock, category
- [ ] Can edit existing product details
- [ ] Can view product list with filtering by category and status
- [ ] Can search products by name
- [ ] System validates all input data
- [ ] Shows appropriate error messages for invalid data

#### Story 2: Stock Monitoring
- **AS A** store manager  
- **I WANT TO** monitor stock levels
- **SO THAT** I can prevent stockouts and overstock

**Acceptance Criteria:**
- [ ] Can view current stock quantity for each product
- [ ] System alerts when stock falls below threshold
- [ ] Can filter products by stock status (in-stock, low-stock, out-of-stock)
- [ ] Can track stock history and changes

#### Story 3: Order Processing
- **AS A** store manager
- **I WANT TO** process customer orders
- **SO THAT** I can fulfill customer demands efficiently

**Acceptance Criteria:**
- [ ] Can create orders with multiple products
- [ ] System automatically updates stock levels
- [ ] Can track order status (pending, confirmed, shipped, delivered)
- [ ] Can view order history and details
- [ ] System prevents orders for out-of-stock items

## 🏗️ Domain Model

### Entities

#### Product
- **id**: UUID (Primary Key)
- **name**: String (required, 1-100 chars)
- **description**: String (optional, max 500 chars)
- **price**: Number (required, min 0)
- **stock**: Integer (required, min 0)
- **category**: Enum (electronics, clothing, books, home)
- **active**: Boolean (default true)
- **createdAt**: DateTime
- **updatedAt**: DateTime

#### Order
- **id**: UUID (Primary Key)
- **customerId**: UUID (required)
- **status**: Enum (pending, confirmed, shipped, delivered, cancelled)
- **total**: Number (calculated from items)
- **items**: Array[OrderItem]
- **shippingAddress**: Object
- **orderDate**: DateTime

#### OrderItem
- **orderId**: UUID (Foreign Key)
- **productId**: UUID (Foreign Key)
- **quantity**: Integer (min 1)
- **unitPrice**: Number (price at time of order)
- **subtotal**: Number (calculated)

### Business Rules

1. **Stock Management**
   - Stock cannot be negative
   - Active products should have stock > 0 or allow backorders
   - Stock updates must be atomic

2. **Order Processing**
   - Order total must equal sum of item subtotals
   - Cannot modify shipped orders
   - Must have at least one item per order

3. **Product Validation**
   - Product names must be unique
   - Price must be positive
   - Category must be from predefined list

## 🎨 Generated UI Components

Using `ae-ui scaffold`, the following components are auto-generated:

### Pages
- `/product` - Product list with search and filtering
- `/product/new` - Create new product form
- `/product/[id]` - Product details and edit
- `/order` - Order management interface
- `/order/new` - Create new order
- `/order/[id]` - Order details and tracking

### Components
- `ProductForm` - React Hook Form with Zod validation
- `ProductCard` - Display component for product grid
- `OrderForm` - Multi-item order creation
- `OrderCard` - Order summary display

### Stories (Storybook)
- Product component variations
- Order component states
- Error and loading states
- Responsive design showcase

### E2E Tests (Playwright)
- Complete user workflows
- Acceptance criteria validation
- Cross-browser compatibility
- Accessibility compliance

## 🚀 Quick Start

### 1. Generate UI from Domain Model

```bash
# Generate all UI components
npx ae-ui scaffold generate

# Or generate specific entity
npx ae-ui scaffold generate --entity Product
```

### 2. Run Development Server

```bash
# Start all services
npm run dev:web

# Start Storybook
npm run dev:storybook
```

### 3. Run Quality Gates

```bash
# Accessibility tests
npm run test:a11y

# Visual regression tests
npm run test:visual

# E2E tests
npm run test:e2e

# Full CI pipeline
npm run test && npm run lint && npm run build:frontend
```

## 📊 Success Metrics

### Technical Validation
- ✅ All TypeScript compilation passes
- ✅ ESLint rules compliance
- ✅ Accessibility (WCAG 2.1 AA) compliance
- ✅ Visual regression tests pass
- ✅ E2E tests cover all acceptance criteria
- ✅ Performance benchmarks met

### Business Validation
- ✅ Complete CRUD operations for Products
- ✅ Order workflow from creation to fulfillment
- ✅ Stock level monitoring and alerts
- ✅ User-friendly error handling
- ✅ Responsive design across devices

## 🎬 Demo Walkthrough

1. **Start from User Stories** → Domain modeling complete
2. **Run UI Scaffold** → 7 files generated per entity
3. **Quality Gates** → All CI checks pass
4. **Live Demo** → Functional inventory system

## 🔗 Related

- Parent Issue: [#53 - Phase 6: UI/UX & Frontend Delivery](https://github.com/itdojp/ae-framework/issues/53)
- Phase 6 Documentation: [docs/phase-6-uiux.md](../../docs/phase-6-uiux.md)
- UI Scaffold Guide: [CLI Reference](../../README.md#ae-ui-scaffold)
