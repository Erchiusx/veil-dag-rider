#!/usr/bin/env sh
set -eu

LEAN_SYSROOT="${LEAN_SYSROOT:-/home/erchius/.elan/toolchains/leanprover--lean4---v4.27.0}"

for arg in "$@"; do
  if [ "$arg" = "-c" ]; then
    exec cc "$@"
  fi
done

exec "$LEAN_SYSROOT/bin/clang" \
  -fuse-ld=lld \
  -L "$LEAN_SYSROOT/lib" \
  -L "$LEAN_SYSROOT/lib/lean" \
  "$@" \
  -Wl,-Bstatic -lunwind -Wl,-Bdynamic
