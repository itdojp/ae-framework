# E-Commerce Platform Specification

> 🌍 Language / 言語: English | 日本語

A modern e-commerce platform for online retail operations.

## Glossary

- **User**: A person who interacts with the system as customer or admin
- **Product**: An item available for purchase in the catalog
- **Order**: A collection of products requested by a user
- **Cart**: Temporary collection of products before checkout
- **Inventory**: Stock management system for products

## Domain

### User
- **id** (UUID, required) - Unique user identifier
- **email** (string, required) - User email address for login
- **name** (string, required) - User display name
- **role** (enum: customer|admin) - User role in the system
- **createdAt** (datetime, required) - Account creation timestamp
- **lastLoginAt** (datetime) - Last login timestamp

### Product
- **id** (UUID, required) - Unique product identifier
- **name** (string, required) - Product display name
- **description** (text) - Detailed product description
- **price** (decimal, required) - Product price in USD
- **stock** (integer, required) - Available quantity in inventory
- **category** (string, required) - Product category
- **isActive** (boolean, required) - Whether product is available for sale

### Order
- **id** (UUID, required) - Unique order identifier
- **userId** (UUID, required) - Reference to ordering user
- **status** (enum: pending|processing|shipped|delivered|cancelled, required) - Order status
- **totalAmount** (decimal, required) - Total order value
- **createdAt** (datetime, required) - Order creation timestamp
- **shippingAddress** (text, required) - Delivery address

### OrderItem
- **id** (UUID, required) - Unique order item identifier  
- **orderId** (UUID, required) - Reference to parent order
- **productId** (UUID, required) - Reference to ordered product
- **quantity** (integer, required) - Number of items ordered
- **unitPrice** (decimal, required) - Price per item at time of order

## Invariants

- User email must be unique across the system
- Product price must be greater than zero
- Product stock cannot be negative
- Order total amount must equal sum of order items
- Order items quantity must be greater than zero
- Order items unit price must be greater than zero
- User cannot order more items than available stock

## Use Cases

### User Registration
- User provides email, name, and password
- System validates email uniqueness  
- System validates password strength
- System creates user account with customer role
- System sends email verification

### Product Catalog Browsing
- User views list of active products
- User can filter by category
- User can search by name or description
- User views detailed product information
- System shows current stock availability

### Add to Cart
- User selects product and quantity
- System validates product availability
- System checks stock quantity
- System adds item to user's cart
- System updates cart total

### Checkout Process
- User reviews cart contents
- User provides shipping address
- User selects payment method
- System validates cart items availability
- System calculates total amount
- System processes payment
- System creates order with pending status
- System reduces product stock
- System sends order confirmation

### Order Management
- Admin views all orders
- Admin can update order status
- Admin can cancel pending orders
- System notifies user of status changes
- System tracks order fulfillment

## API

- POST /auth/register - Register new user account
- POST /auth/login - User authentication
- GET /users/{id} - Get user profile
- PUT /users/{id} - Update user profile
- GET /products - List products with filtering
- GET /products/{id} - Get product details
- POST /products - Create new product (admin only)
- PUT /products/{id} - Update product (admin only)
- DELETE /products/{id} - Deactivate product (admin only)
- GET /cart - Get user's cart contents
- POST /cart/items - Add item to cart
- PUT /cart/items/{id} - Update cart item quantity
- DELETE /cart/items/{id} - Remove item from cart
- POST /orders - Create new order (checkout)
- GET /orders - Get user's order history
- GET /orders/{id} - Get order details
- PUT /orders/{id}/status - Update order status (admin only)

## UI Requirements

### Product Catalog Page
- Grid layout showing product cards
- Each card shows image, name, price, stock status
- Filter sidebar by category
- Search bar for product name
- Pagination for large catalogs

### Product Detail Page  
- Large product image
- Product name, description, price
- Stock quantity indicator
- Add to cart button with quantity selector
- Related products section

### Shopping Cart Page
- List of cart items with images
- Quantity adjustment controls
- Remove item functionality
- Running total calculation
- Checkout button

### Checkout Page
- Cart summary
- Shipping address form
- Payment method selection
- Order total breakdown
- Place order confirmation

## Non-Functional Requirements

### Performance
- Product catalog page load: < 2 seconds
- Search response time: < 1 second  
- Checkout process: < 5 seconds
- API response time: < 500ms for 95% of requests

---

## 日本語（概要）

本ドキュメントは、オンライン小売を対象としたモダンな EC プラットフォームの AE-Spec（例）です。用語集、ドメイン（エンティティ/属性）、不変条件、ユースケース、API、UI 要件、非機能要件を含み、AE-IR への変換や各フェーズ（テスト生成/コード生成/検証）の入力として利用できます。

### ドメイン（抜粋）
- User: id/email/name/role/timestamps
- Product: id/name/description/price/stock/category/isActive
- Order/OrderItem: 受注、注文明細、合計、ステータス

### 不変条件（例）
- メールは一意
- 価格は 0 より大
- 在庫は負数不可
- 注文合計は注文明細の合計に一致

### UI 要件（抜粋）
- カタログ一覧/詳細、カート、チェックアウト、注文履歴

### 非機能要件（例）
- カタログ表示 < 2 秒、検索 < 1 秒、Checkout < 5 秒
- API p95 < 500ms、JWT 認証、bcrypt でパスワードハッシュ

このサンプルは実際のプロジェクトに合わせて自由に拡張/修正してください。

### Security
- User passwords must be hashed using bcrypt
- API endpoints require JWT authentication
- Admin operations require role-based authorization
- Payment information must be encrypted in transit

### Scalability  
- Support 10,000 concurrent users
- Handle 1 million products in catalog
- Process 1000 orders per minute during peak
- Database must support read replicas

### Reliability
- 99.9% uptime availability
- Graceful handling of payment failures
- Order data persistence across system failures
- Automatic backup of critical data
