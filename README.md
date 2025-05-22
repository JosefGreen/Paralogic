# Paralogic

Paralogic is a multidisciplinary mathematical theory of insight and creative dynamics, developed by Josef I Green.  
We currently rely on local builds to ensure the formal proofs type-check.
This repository contains:

- **Python code** for core tension & jump operators, with unit tests and CI.  
- **Lean 4 formalization** of theorems in `src/`, verified locally via Lake.  
- **Treatise documents** in `docs/`, culminating in `Paralogic_Master.docx`.

---

## Quick Start

### Python Setup & Tests

```bash
# From repo root
python -m venv venv
.\venv\Scripts\activate     # Windows PowerShell
pip install -r python/requirements.txt
pytest python/tests -q
