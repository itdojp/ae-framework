'use client';

import {useForm} from 'react-hook-form';
import {zodResolver} from '@hookform/resolvers/zod';
import {z} from 'zod';
import {Button} from '@ae-framework/ui/components/button';
import {Input} from '@ae-framework/ui/components/input';
import {Textarea} from '@ae-framework/ui/components/textarea';
import {Checkbox} from '@ae-framework/ui/components/checkbox';
import {Select, SelectContent, SelectItem, SelectTrigger, SelectValue} from '@ae-framework/ui/components/select';

// Zod schema for Product validation
const productSchema = z.object({
  name: z.string().min(1).max(100),
  description: z.string().max(500).optional(),
  price: z.number().min(0),
  stock: z.number().min(0).int(),
  lowStockThreshold: z.number().min(0).int(),
  category: z.enum(["electronics"]),
  sku: z.string(),
  weight: z.number().min(0).optional(),
  dimensions: z.any().optional(),
  active: z.boolean(),
  tags: z.array(z.any()).optional(),
});

type ProductFormData = z.infer<typeof productSchema>;

interface ProductFormProps {
  initialData?: Partial<ProductFormData>;
  onSubmit: (data: ProductFormData) => void;
  onCancel?: () => void;
  isLoading?: boolean;
  error?: string;
}

export function ProductForm({
  initialData, 
  onSubmit, 
  onCancel, 
  isLoading = false,
  error 
}: ProductFormProps) {
  const {
    register,
    handleSubmit,
    formState: {errors},
    setValue,
    watch
 } = useForm<ProductFormData>({
    resolver: zodResolver(productSchema),
    defaultValues: initialData
 });

  return (
    <form onSubmit={handleSubmit(onSubmit)} className="space-y-6">
      {error && (
        <div className="bg-red-50 border border-red-200 rounded-md p-3">
          <p className="text-red-800 text-sm">{error}</p>
        </div>
      )}

      <div>
        <label htmlFor="name" className="block text-sm font-medium text-gray-700 mb-1">
          Name *
        </label>
        <Textarea
          id="name"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('name')}
          className={errors.name ? 'border-red-500' : ''}
        />
        {errors.name && (
          <p className="text-red-600 text-sm mt-1">
            {errors.name?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="description" className="block text-sm font-medium text-gray-700 mb-1">
          Description
        </label>
        <Textarea
          id="description"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('description')}
          className={errors.description ? 'border-red-500' : ''}
        />
        {errors.description && (
          <p className="text-red-600 text-sm mt-1">
            {errors.description?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="price" className="block text-sm font-medium text-gray-700 mb-1">
          Price *
        </label>
        <Input
          id="price"
          type="number"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('price', {valueAsNumber: true})}
          className={errors.price ? 'border-red-500' : ''}
        />
                {errors.price && (
          <p className="text-red-600 text-sm mt-1">
            {errors.price?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="stock" className="block text-sm font-medium text-gray-700 mb-1">
          Stock *
        </label>
        <Input
          id="stock"
          type="number"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('stock', {valueAsNumber: true})}
          className={errors.stock ? 'border-red-500' : ''}
        />
                {errors.stock && (
          <p className="text-red-600 text-sm mt-1">
            {errors.stock?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="lowStockThreshold" className="block text-sm font-medium text-gray-700 mb-1">
          Low Stock Threshold *
        </label>
        <Input
          id="lowStockThreshold"
          type="number"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('lowStockThreshold', {valueAsNumber: true})}
          className={errors.lowStockThreshold ? 'border-red-500' : ''}
        />
                {errors.lowStockThreshold && (
          <p className="text-red-600 text-sm mt-1">
            {errors.lowStockThreshold?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="category" className="block text-sm font-medium text-gray-700 mb-1">
          Category *
        </label>
        <Textarea
          id="category"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('category')}
          className={errors.category ? 'border-red-500' : ''}
        />
        {errors.category && (
          <p className="text-red-600 text-sm mt-1">
            {errors.category?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="sku" className="block text-sm font-medium text-gray-700 mb-1">
          Sku *
        </label>
        <Textarea
          id="sku"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('sku')}
          className={errors.sku ? 'border-red-500' : ''}
        />
        {errors.sku && (
          <p className="text-red-600 text-sm mt-1">
            {errors.sku?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="weight" className="block text-sm font-medium text-gray-700 mb-1">
          Weight
        </label>
        <Input
          id="weight"
          type="number"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('weight', {valueAsNumber: true})}
          className={errors.weight ? 'border-red-500' : ''}
        />
                {errors.weight && (
          <p className="text-red-600 text-sm mt-1">
            {errors.weight?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="dimensions" className="block text-sm font-medium text-gray-700 mb-1">
          Dimensions
        </label>
        <Input
          id="dimensions"
          type="text"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('dimensions')}
          className={errors.dimensions ? 'border-red-500' : ''}
        />
                {errors.dimensions && (
          <p className="text-red-600 text-sm mt-1">
            {errors.dimensions?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="active" className="block text-sm font-medium text-gray-700 mb-1">
          Active *
        </label>
        <div className="flex items-center space-x-2">
          <Checkbox
            id="active"
            {...register('active')}
            className={errors.active ? 'border-red-500' : ''}
          />
          <label htmlFor="active" className="text-sm text-gray-600">
            Whether product is available for sale
          </label>
        </div>
        {errors.active && (
          <p className="text-red-600 text-sm mt-1">
            {errors.active?.message}
          </p>
        )}
      </div>

      <div>
        <label htmlFor="tags" className="block text-sm font-medium text-gray-700 mb-1">
          Tags
        </label>
        <Input
          id="tags"
          type="text"
          placeholder="Product entity for inventory management with comprehensive validation"
          {...register('tags')}
          className={errors.tags ? 'border-red-500' : ''}
        />
                {errors.tags && (
          <p className="text-red-600 text-sm mt-1">
            {errors.tags?.message}
          </p>
        )}
      </div>

      <div className="flex gap-3 pt-4">
        <Button 
          type="submit" 
          disabled={isLoading}
          className="flex-1"
        >
          {isLoading ? 'Saving...' : initialData ? 'Update Product' : 'Create Product'}
        </Button>
        
        {onCancel && (
          <Button 
            type="button" 
            variant="outline"
            onClick={onCancel}
            disabled={isLoading}
          >
            Cancel
          </Button>
        )}
      </div>
    </form>
  );
}