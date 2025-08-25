#!/bin/bash

# Branch Protection Setup Helper
# Requires admin privileges to execute

OWNER=$(git remote get-url origin | sed -E 's#.*[:/](.+)/(.+)\.git#\1#')
REPO=$(git remote get-url origin | sed -E 's#.*[:/](.+)/(.+)\.git#\2#')

echo "Branch Protection Setup Command for $OWNER/$REPO:"
echo ""
echo "gh api -X PUT repos/$OWNER/$REPO/branches/main/protection \\"
echo "  -f required_status_checks.strict=true \\"
echo "  -f required_status_checks.contexts[]=\"PR Verify / verify\" \\"
echo "  -f enforce_admins=true \\"
echo "  -f required_pull_request_reviews.required_approving_review_count=1 \\"
echo "  -f restrictions=\"\""
echo ""
echo "Note: Requires admin privileges on the repository"