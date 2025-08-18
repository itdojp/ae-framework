// Tailwind CSS configuration using design tokens
import { colors, typography, spacing, borderRadius, shadows, breakpoints } from './index';

export const tailwindTokens = {
  colors: {
    primary: colors.primary,
    gray: colors.gray,
    success: colors.semantic.success,
    warning: colors.semantic.warning,
    error: colors.semantic.error,
    info: colors.semantic.info,
  },
  fontFamily: typography.fontFamily,
  fontSize: typography.fontSize,
  fontWeight: typography.fontWeight,
  lineHeight: typography.lineHeight,
  spacing,
  borderRadius,
  boxShadow: shadows,
  screens: breakpoints,
};

export default tailwindTokens;