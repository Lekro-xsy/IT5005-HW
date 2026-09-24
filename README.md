# IT5005 Sudoku Knowledge Representation Assignment

This repository contains a propositional-logic Sudoku solver and its Streamlit interface.

## Contents

- `Sudoku_Assignment.ipynb` - executed experiments and conceptual answers
- `sudoku_solver.py` - general CNF and definite-clause encodings, forward chaining, and tabled backward chaining
- `sudoku_app.py` - interactive solver, entailment queries, timings, and tutor-mode proof traces
- `logic_.py`, `utils.py`, `puzzles.json` - supplied runtime support files

## Run locally

```bash
python -m venv .venv
# Windows: .venv\Scripts\activate
# macOS/Linux: source .venv/bin/activate
pip install -r requirements.txt
streamlit run sudoku_app.py
```

The app does not use the `solution` entries from `puzzles.json`; they are used only by the notebook's validation cells.
