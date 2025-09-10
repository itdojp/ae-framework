// Model for Reservation (from OpenAPI)
export interface Reservation {
  id: string
  sku: string
  quantity: number
  orderId: string
  status: 'created' | 'canceled'
}

