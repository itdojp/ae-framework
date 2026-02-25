export type InventoryItem = {
  id: string;
  stock: number;
};

export function reserveInventory(item: InventoryItem, quantity: number): boolean {
  return item.stock >= quantity;
}

export function releaseInventory(item: InventoryItem, quantity: number): boolean {
  return item.stock + quantity >= 0;
}
