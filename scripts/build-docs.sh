#!/usr/bin/env bash
set -euo pipefail

site_dir="${SITE_DIR:-site}"

python -m mkdocs build --strict --site-dir "$site_dir"
install -m 0644 llms.txt "$site_dir/llms.txt"

test -s "$site_dir/index.html"
test -s "$site_dir/llms.txt"
