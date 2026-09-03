#!/usr/bin/env python3
"""Verify intentionally repeated scientific cells across registered evidence blocks.

Shared cell IDs are reproducibility anchors, not independent replicates.  For
every shared cell, all non-runtime result fields must agree after row alignment.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import pandas as pd
import numpy as np

RUNTIME_TOKENS=("runtime","elapsed")
EXCLUDE={"_source_shard","trace_file"}
KEYS=["cell_id","evaluation_scope","target"]


def load(path: Path) -> pd.DataFrame:
    """Load one merged result block with stable string typing for cell identifiers."""
    d=pd.read_csv(path, dtype={"cell_id":"string"})
    d["target"]=d.get("target","").fillna("").astype(str)
    return d

def comparable_columns(a: pd.DataFrame,b: pd.DataFrame):
    """Select scientific columns that should agree across overlapping experiment blocks."""
    return [c for c in a.columns if c in b.columns and c not in EXCLUDE and not any(t in c for t in RUNTIME_TOKENS)]

def compare_pair(name_a,a,name_b,b):
    """Compare overlapping scientific cells between two experiment blocks."""
    shared=sorted(set(a.cell_id.astype(str)) & set(b.cell_id.astype(str)))
    diffs=[]
    cols=comparable_columns(a,b)
    for cid in shared:
        x=a[a.cell_id.astype(str)==cid].sort_values(KEYS).reset_index(drop=True)
        y=b[b.cell_id.astype(str)==cid].sort_values(KEYS).reset_index(drop=True)
        if len(x)!=len(y):
            diffs.append({"cell_id":cid,"reason":"row_count","left":len(x),"right":len(y)})
            continue
        for c in cols:
            xs=x[c]; ys=y[c]
            if pd.api.types.is_numeric_dtype(xs) and pd.api.types.is_numeric_dtype(ys):
                xv=xs.to_numpy(dtype=float); yv=ys.to_numpy(dtype=float)
                same=bool(np.allclose(xv,yv,rtol=1e-12,atol=1e-12,equal_nan=True))
            else:
                same=xs.fillna("<NA>").astype(str).eq(ys.fillna("<NA>").astype(str)).all()
            if not same:
                diffs.append({"cell_id":cid,"reason":"column_mismatch","column":c})
                break
    return {"left":name_a,"right":name_b,"shared_cell_ids":len(shared),"differences":diffs[:50],"pass":not diffs}

def main():
    """Verify scientific consistency across registered experiment blocks with shared cells."""
    ap=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--primary',required=True)
    ap.add_argument('--alpha',required=True)
    ap.add_argument('--retention',required=True)
    ap.add_argument('--out',required=True)
    a=ap.parse_args()
    frames={
      'primary':load(Path(a.primary)/'results.csv'),
      'alpha':load(Path(a.alpha)/'results.csv'),
      'retention':load(Path(a.retention)/'results.csv'),
    }
    pairs=[compare_pair('primary',frames['primary'],'alpha',frames['alpha']),
           compare_pair('primary',frames['primary'],'retention',frames['retention']),
           compare_pair('alpha',frames['alpha'],'retention',frames['retention'])]
    expected={('primary','alpha'):180,('primary','retention'):40,('alpha','retention'):40}
    counts_ok=all(p['shared_cell_ids']==expected[(p['left'],p['right'])] for p in pairs)
    payload={'pass':bool(counts_ok and all(p['pass'] for p in pairs)),
             'expected_shared_cell_ids':{f'{k[0]}__{k[1]}':v for k,v in expected.items()},
             'pair_audits':pairs,
             'numeric_tolerance':{'rtol':1e-12,'atol':1e-12},
             'interpretation':'Shared cells are deterministic cross-block reproducibility anchors; numeric fields must agree to machine-precision tolerance and shared cells must not be counted as independent Monte-Carlo evidence.'}
    Path(a.out).write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(payload,indent=2))
    raise SystemExit(0 if payload['pass'] else 2)

if __name__=='__main__': main()
