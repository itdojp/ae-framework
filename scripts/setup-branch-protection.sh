#!/bin/bash
# Branch Protection Setup Script for ae-framework
# Requires: gh CLI with admin permissions

set -e

REPO="itdojp/ae-framework"
BRANCH="main"

echo "🔒 Setting up branch protection for $REPO:$BRANCH"

# Check if user has admin permissions
if ! gh auth status &>/dev/null; then
    echo "❌ Error: GitHub CLI not authenticated. Run 'gh auth login' first."
    exit 1
fi

# Apply branch protection rules
echo "📋 Applying branch protection rules..."

# Create protection payload
cat > /tmp/protection-payload.json << 'EOF'
{
  "required_status_checks": {
    "strict": true,
    "contexts": ["PR Verify / verify"]
  },
  "enforce_admins": true,
  "required_pull_request_reviews": {
    "required_approving_review_count": 1,
    "dismiss_stale_reviews": true,
    "require_code_owner_reviews": false
  },
  "restrictions": null,
  "allow_force_pushes": false,
  "allow_deletions": false
}
EOF

gh api repos/$REPO/branches/$BRANCH/protection \
    --method PUT \
    --input /tmp/protection-payload.json

echo "✅ Branch protection configured successfully!"
echo ""
# Cleanup temp file
rm -f /tmp/protection-payload.json

echo "📊 Protection rules applied:"
echo "  • Required status checks: PR Verify / verify"
echo "  • Require branches to be up to date: true"
echo "  • Restrict pushes to matching branches: false"
echo "  • Require pull request reviews: 1 approval"
echo "  • Dismiss stale reviews: true"
echo "  • Enforce for administrators: true"
echo "  • Allow force pushes: false"
echo "  • Allow deletions: false"
echo ""
echo "🔍 Verify settings at: https://github.com/$REPO/settings/branches"