import re
import json
import nbformat as nbf
from nbformat.v4 import new_markdown_cell, new_code_cell

def parse_py_to_notebook(py_file):
    with open(py_file, 'r') as f:
        content = f.read()

    cells = []
    # Split on # %% 
    parts = re.split(r'# %% \[markdown\](.*?)', content, flags=re.DOTALL | re.MULTILINE)
    
    i = 0
    while i < len(parts):
        if i % 2 == 1:  # markdown part
            md = parts[i].strip()
            if md:
                cells.append(new_markdown_cell(md))
        i += 1
    
    # Code parts
    code_blocks = re.split(r'# %% \[markdown\]', content, flags=re.MULTILINE)
    for code in code_blocks:
        code = code.strip()
        if code and not code.startswith('# %%'):
            cells.append(new_code_cell(code))
    
    nb = nbf.v4.new_notebook()
    nb.cells = cells
    return nb

nb = parse_py_to_notebook('ancillary/montecarlo_yukawa.py')
with open('ancillary/junction_montecarlo.ipynb', 'w') as f:
    nbf.write(nb, f)
print("Generated ancillary/junction_montecarlo.ipynb")