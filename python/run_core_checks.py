"""Run the executable Paralogic / ISFT finite core checks."""

from __future__ import annotations

import json
import sys

try:
    from .paralogic_isft_core import run_all_checks
except ImportError:
    from paralogic_isft_core import run_all_checks


def main() -> int:
    results = run_all_checks()
    print(json.dumps(results, indent=2))
    return 0 if results["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
