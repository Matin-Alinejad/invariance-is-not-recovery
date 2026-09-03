"""Regenerate reference figures and computational/result tables from processed evidence."""
from pathlib import Path
import argparse
import math
import sys
import logging
import yaml
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib as mpl
from matplotlib.lines import Line2D

logging.getLogger('fontTools').setLevel(logging.WARNING)
logging.getLogger('fontTools.subset').setLevel(logging.WARNING)

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'code'))
from experiments.run_recovery_experiments import calibrated_sample_size

_parser=argparse.ArgumentParser(description='Regenerate the six reference figures and eight computational/result LaTeX tables from processed evidence.')
_parser.add_argument('--evidence-dir', default=str(ROOT/'evidence'))
_parser.add_argument('--output-dir', default=str(ROOT/'results'/'regenerated_artifacts'))
_args=_parser.parse_args()
D=Path(_args.evidence_dir).resolve()
OUT=Path(_args.output_dir).resolve()
FIG=OUT/'figures'; TAB=OUT/'tables'; DER=OUT/'derived'
for x in [FIG,TAB,DER]: x.mkdir(parents=True,exist_ok=True)

# ---------------------------------------------------------------------------
# Reference figure style, authored at release dimensions.
# Full-width reference figures are authored at exactly 6 inches to preserve
# consistent typography when reused in downstream documents.
# Palette: high-contrast colour-blind-safe Okabe--Ito / Color Universal
# Design colours. The reference condition stays neutral charcoal so hue is
# reserved for scientific contrasts; markers/line styles remain redundant.
# ---------------------------------------------------------------------------
INK='#252525'
MID='#676767'
HAIR='#D9DEE3'
PAPER='#FFFFFF'
# Paul Tol vibrant qualitative palette: colour-blind safe, high-contrast,
# and deliberately vivid without using neon or rainbow hues. Hue is never
# the sole encoding; markers, fill and line style remain redundant.
COMPLETE='#0077BB'   # clear blue reference
QUAD='#EE7733'       # vivid orange theorem-aligned arm
LOGISTIC='#009988'   # blue-green stress arm
ER='#0077BB'
RR='#009988'
SW='#EE7733'
SF='#AA3377'         # distinct purple for topology-only encodings
SOFT_BLUE='#33BBEE'
SOFT_TEAL='#009988'
SOFT_GOLD='#EE7733'
SOFT_ROSE='#EE3377'

mpl.rcParams.update({
    'font.family':'serif',
    'font.serif':['Tinos','TeX Gyre Termes','Times New Roman','Times'],
    'mathtext.fontset':'stix',
    'font.size':9.4,
    'axes.labelsize':9.6,
    'axes.titlesize':9.7,
    'legend.fontsize':9.0,
    'xtick.labelsize':9.1,
    'ytick.labelsize':9.1,
    'axes.linewidth':0.75,
    'lines.linewidth':2.0,
    'lines.markersize':5.8,
    'axes.grid':False,
    'axes.axisbelow':True,
    'pdf.fonttype':42,
    'ps.fonttype':42,
    'savefig.facecolor':'white',
    'figure.facecolor':'white',
})

GEOMETRY=[]
def save_figure(fig, name):
    """Validate figure geometry and export publication PDF/PNG assets."""
    # Enforce the release design contract: every data axis is landscape
    # (x extent >= y extent) at the exact 6-inch reference width.
    fig.canvas.draw()
    fw, fh = fig.get_size_inches()
    if abs(fw - 6.0) > 1e-8:
        raise RuntimeError(f'{name}: figure width {fw:.3f} in is not 6.0 in')
    for i, ax in enumerate(fig.axes):
        bb=ax.get_window_extent().transformed(fig.dpi_scale_trans.inverted())
        ok=bb.width + 1e-9 >= bb.height
        GEOMETRY.append({'figure':name,'axis':i,'axis_width_in':bb.width,'axis_height_in':bb.height,'landscape_ok':ok})
        if not ok:
            raise RuntimeError(f'{name} axis {i}: width {bb.width:.3f} < height {bb.height:.3f}')
    fig.savefig(FIG/f'{name}.pdf', dpi=300)
    fig.savefig(FIG/f'{name}.png', dpi=360)
    plt.close(fig)

def style_axes(ax, *, ygrid=True, xgrid=False):
    """Apply the shared publication axis treatment."""
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['left'].set_color('#777C82')
    ax.spines['bottom'].set_color('#777C82')
    ax.tick_params(length=3.0, width=.72, color='#777C82', pad=2.5)
    if ygrid:
        ax.grid(axis='y', color=HAIR, lw=.55, alpha=.72)
    if xgrid:
        ax.grid(axis='x', color=HAIR, lw=.55, alpha=.72)

def asymmetric_error_bars(mean, lo, hi):
    """Convert lower/upper interval endpoints to Matplotlib asymmetric errors."""
    return np.vstack([np.asarray(mean)-np.asarray(lo),np.asarray(hi)-np.asarray(mean)])

def format_scientific_tex(x):
    """Format a scalar in compact scientific notation for LaTeX tables."""
    mant, exp = f'{float(x):.2e}'.split('e')
    return rf'{mant}\times10^{{{int(exp)}}}'

def write_latex_row(handle, row_text):
    """Write one escaped row terminator to a generated LaTeX table."""
    handle.write(row_text + r' \\' + '\n')

primary20=pd.read_csv(D/'primary_scaling_20_seeds'/'analysis'/'summary.csv')
primary10=pd.read_csv(D/'primary_scaling_10_seeds'/'analysis'/'summary.csv')
paired10=pd.read_csv(D/'primary_scaling_10_seeds'/'analysis'/'paired_contrasts.csv')
alpha=pd.read_csv(D/'significance_threshold_sensitivity'/'analysis'/'paired_contrasts.csv')
ret=pd.read_csv(D/'retention_sensitivity'/'analysis'/'retention_summary.csv')
retpair=pd.read_csv(D/'retention_sensitivity'/'analysis'/'retention_paired_contrasts.csv')
local=pd.read_csv(D/'matched_local_global'/'analysis'/'matched_local_global_paired.csv')
depth=pd.read_csv(D/'depth_scope.csv')
margins=pd.read_csv(D/'population_margins.csv')
gates=pd.read_csv(D/'experiment_program_summary.csv')

# ---------------------------------------------------------------------------
# Figure 1 is intentionally NOT generated here. It is a native LaTeX/TikZ
# schematic (`reference/figures/recovery_pipeline.tex`), so its typography and
# geometry are owned by the native TeX source rather than by Matplotlib.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Figure 2. Primary recovery. Complete-data reference is neutral charcoal;
# theorem-aligned quadratic selection gets the sole strong blue accent; the
# logistic stress arm is a muted rose. CI bands are deliberately understated.
# ---------------------------------------------------------------------------
name={'complete':'Complete','self_masking_gaussian_preserving':'Quadratic','self_masking_logistic_population':'Logistic'}
col={'complete':COMPLETE,'self_masking_gaussian_preserving':QUAD,'self_masking_logistic_population':LOGISTIC}
mode_marker={'complete':'o','self_masking_gaussian_preserving':'s','self_masking_logistic_population':'^'}
fig,axes=plt.subplots(1,2,figsize=(6.0,2.42),sharey=True)
for j,(ax,topo,title) in enumerate(zip(axes,['random_regular_d2','small_world_k2'],['Random regular','Small world'])):
    for mode in name:
        d=primary20[(primary20.evaluation_scope=='global_whole_skeleton')&(primary20.topology==topo)&(primary20.gamma==1.0)&(primary20.missingness_mode==mode)].sort_values('p')
        ax.fill_between(d.p,100*d.f1_lo95,100*d.f1_hi95,color=col[mode],alpha=.075,lw=0)
        ax.plot(d.p,100*d.f1_mean,marker=mode_marker[mode],mec='white',mew=.7,color=col[mode],label=name[mode],zorder=3)
    ax.set_ylim(98.2,100.15)
    ax.set_xlabel('Number of variables $p$')
    ax.set_xticks(sorted(primary20[primary20.topology==topo].p.unique()))
    style_axes(ax)
axes[0].set_ylabel('$F_1$ (%)')
for ax in axes: ax.yaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
handles,labels=axes[0].get_legend_handles_labels()
fig.legend(handles,labels,loc='upper center',bbox_to_anchor=(.5,.985),ncol=3,frameon=False,handlelength=1.7,handletextpad=.45,columnspacing=1.50,borderaxespad=0,alignment='center')
fig.subplots_adjust(left=.115,right=.995,bottom=.235,top=.825,wspace=.16)
save_figure(fig,'primary_scaling')

# ---------------------------------------------------------------------------
# Figure 3. Operating point with paired 95% intervals in both directions.
# This makes the finite-sample uncertainty visible instead of drawing only a
# path through point estimates.
# ---------------------------------------------------------------------------
q=paired10[(paired10.contrast=='quadratic_minus_complete')&(paired10.alpha_schedule=='n_inverse_half')&(paired10.gamma==1.0)&(paired10.evaluation_scope=='global_whole_skeleton')]
q=q[q.topology.isin(['random_regular_d2','small_world_k2'])].copy()
fig,ax=plt.subplots(figsize=(6.0,2.48))
ax.axhline(0,color='#777C82',ls=(0,(3,2)),lw=.9,zorder=0)
ax.axvline(0,color='#777C82',ls=(0,(3,2)),lw=.9,zorder=0)
for topo,c,label,mk in [('random_regular_d2',RR,'Random regular','o'),('small_world_k2',SW,'Small world','s')]:
    d=q[q.topology==topo].sort_values('p')
    xx=100*d.recall_delta_mean.to_numpy(); yy=100*d.precision_delta_mean.to_numpy()
    xlo=100*d.recall_delta_lo95.to_numpy(); xhi=100*d.recall_delta_hi95.to_numpy()
    ylo=100*d.precision_delta_lo95.to_numpy(); yhi=100*d.precision_delta_hi95.to_numpy()
    ax.errorbar(xx,yy,xerr=asymmetric_error_bars(xx,xlo,xhi),yerr=asymmetric_error_bars(yy,ylo,yhi),fmt='none',ecolor=c,elinewidth=.75,alpha=.33,capsize=0,zorder=1)
    ax.plot(xx,yy,color=c,lw=1.8,alpha=.95,zorder=2)
    ax.scatter(xx,yy,s=34,marker=mk,color=c,edgecolor='white',linewidth=.7,zorder=3)
    first=d.iloc[0]; last=d.iloc[-1]
    ax.annotate(f'$p={int(first.p)}$',(100*first.recall_delta_mean,100*first.precision_delta_mean),xytext=(5,6),textcoords='offset points',fontsize=9.0,color=c)
    ax.annotate(label,(100*last.recall_delta_mean,100*last.precision_delta_mean),xytext=(-5,9),textcoords='offset points',ha='right',fontsize=9.15,weight='bold',color=c)
ax.set_xlim(-.55,.045); ax.set_ylim(-.18,3.15)
ax.set_xlabel('Recall change (percentage points)')
ax.set_ylabel('Precision change (pp)')
style_axes(ax)
ax.xaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
ax.yaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
fig.subplots_adjust(left=.115,right=.992,bottom=.225,top=.965)
save_figure(fig,'precision_recall_shift')

# ---------------------------------------------------------------------------
# Figure 4. Retention sensitivity. Two compact legends separate semantic
# encodings: colour = topology; line/marker = dimension.
# ---------------------------------------------------------------------------
fig,axes=plt.subplots(1,2,figsize=(6.0,2.42))
styles=[
    ('random_regular_d2',50,RR,'o','-'),
    ('random_regular_d2',100,RR,'s','--'),
    ('small_world_k2',50,SW,'o','-'),
    ('small_world_k2',100,SW,'s','--')]
for topo,pv,c,mk,ls in styles:
    d=ret[(ret.evaluation_scope=='global_whole_skeleton')&(ret.topology==topo)&(ret.p==pv)].sort_values('missing_rate_target')
    x=100*d.missing_rate_target.to_numpy()
    for ax,mean_col,lo_col,hi_col in [
        (axes[0],'f1_mean','f1_lo95','f1_hi95'),
        (axes[1],'trace_ci_effective_fraction_mean_mean','trace_ci_effective_fraction_mean_lo95','trace_ci_effective_fraction_mean_hi95')]:
        y=100*d[mean_col].to_numpy(); lo=100*d[lo_col].to_numpy(); hi=100*d[hi_col].to_numpy()
        ax.fill_between(x,lo,hi,color=c,alpha=.065,lw=0)
        ax.plot(x,y,marker=mk,ls=ls,color=c,mec='white',mew=.6)
axes[0].set_xlabel('Requested missingness (%)'); axes[0].set_ylabel('$F_1$ (%)')
axes[1].set_xlabel('Requested missingness (%)'); axes[1].set_ylabel('Usable records (%)')
for ax in axes:
    ax.set_xticks([10,30,50]); style_axes(ax)
    ax.yaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
legend_handles=[
    Line2D([0],[0],color=RR,lw=2,label='Random regular'),
    Line2D([0],[0],color=SW,lw=2,label='Small world'),
    Line2D([0],[0],color=INK,lw=1.7,marker='o',mfc='white',mec=INK,label='$p=50$'),
    Line2D([0],[0],color=INK,lw=1.7,ls='--',marker='s',mfc='white',mec=INK,label='$p=100$'),
]
fig.legend(handles=legend_handles,loc='upper center',bbox_to_anchor=(.5,.985),ncol=4,frameon=False,handlelength=1.5,handletextpad=.42,columnspacing=1.15,borderaxespad=0,alignment='center')
fig.subplots_adjust(left=.115,right=.995,bottom=.235,top=.825,wspace=.24)
save_figure(fig,'retention_sensitivity')

# ---------------------------------------------------------------------------
# Figure 5. Alpha sensitivity as a genuine forest plot: condition on the y
# axis, paired effect on the x axis, and 95% intervals explicit. This avoids
# a category-on-x scatter because the contrast direction is easier to read.
# ---------------------------------------------------------------------------
a=alpha[(alpha.contrast=='fixed_005_minus_n_inverse_half')&(alpha.evaluation_scope=='global_whole_skeleton')&(alpha.gamma==1.0)].copy()
top_order=['er_expected_degree_2','random_regular_d2','small_world_k2']
short={'er_expected_degree_2':'ER','random_regular_d2':'RR','small_world_k2':'SW'}
cond=[(t,pv) for t in top_order for pv in [50,100]]
mode_order=['complete','self_masking_gaussian_preserving','self_masking_logistic_population']
mode_lab={'complete':'Complete','self_masking_gaussian_preserving':'Quadratic','self_masking_logistic_population':'Logistic'}
mode_col={'complete':COMPLETE,'self_masking_gaussian_preserving':QUAD,'self_masking_logistic_population':LOGISTIC}
mode_mk={'complete':'o','self_masking_gaussian_preserving':'s','self_masking_logistic_population':'^'}
fig,axes=plt.subplots(1,2,figsize=(6.0,2.48),sharey=True)
ybase=np.arange(len(cond))[::-1]
off={'complete':.18,'self_masking_gaussian_preserving':0,'self_masking_logistic_population':-.18}
for mode in mode_order:
    fym=[]; fylo=[]; fyhi=[]; fpm=[]; fplo=[]; fphi=[]; yy=[]
    for idx,(t,pv) in enumerate(cond):
        r=a[(a.topology==t)&(a.p==pv)&(a.missingness_mode==mode)].iloc[0]
        yy.append(ybase[idx]+off[mode])
        fym.append(100*r.f1_delta_mean); fylo.append(100*r.f1_delta_lo95); fyhi.append(100*r.f1_delta_hi95)
        fpm.append(r.fp_delta_mean); fplo.append(r.fp_delta_lo95); fphi.append(r.fp_delta_hi95)
    axes[0].errorbar(fym,yy,xerr=asymmetric_error_bars(fym,fylo,fyhi),fmt=mode_mk[mode],ms=5.3,capsize=1.8,color=mode_col[mode],mec='white',mew=.55,lw=1.15,label=mode_lab[mode])
    axes[1].errorbar(fpm,yy,xerr=asymmetric_error_bars(fpm,fplo,fphi),fmt=mode_mk[mode],ms=5.3,capsize=1.8,color=mode_col[mode],mec='white',mew=.55,lw=1.15,label=mode_lab[mode])
for ax in axes:
    ax.axvline(0,color='#777C82',ls=(0,(3,2)),lw=.9)
    for y in [3.5,1.5]: ax.axhline(y,color=HAIR,lw=.7)
    style_axes(ax,ygrid=False,xgrid=True)
    ax.xaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
axes[0].set_yticks(ybase)
axes[0].set_yticklabels([f'{short[t]}  $p={pv}$' for t,pv in cond])
axes[1].tick_params(axis='y',labelleft=False)
axes[0].set_xlabel(r'$\Delta F_1$ (percentage points)')
axes[1].set_xlabel(r'$\Delta$ false positives')
handles,labels=axes[0].get_legend_handles_labels()
fig.legend(handles,labels,loc='upper center',bbox_to_anchor=(.5,.985),ncol=3,frameon=False,handlelength=1.4,handletextpad=.42,columnspacing=1.40,borderaxespad=0,alignment='center')
fig.subplots_adjust(left=.145,right=.995,bottom=.225,top=.81,wspace=.23)
save_figure(fig,'threshold_sensitivity')

# ---------------------------------------------------------------------------
# Figure 6. Matched local validation. Alternating topology bands turn the
# paired-condition strip into a readable journal forest plot without adding
# decorative colour. Colour = missingness regime; fill = p.
# ---------------------------------------------------------------------------
L=local.copy()
top_order=['er_expected_degree_2','random_regular_d2','small_world_k2','scale_free_m2']
top_lab={'er_expected_degree_2':'Erdős–Rényi','random_regular_d2':'Random regular','small_world_k2':'Small world','scale_free_m2':'Scale free'}
mode_order=['complete','self_masking_gaussian_preserving','self_masking_logistic_population']
mode_col={'complete':COMPLETE,'self_masking_gaussian_preserving':QUAD,'self_masking_logistic_population':LOGISTIC}
mode_mk={'complete':'o','self_masking_gaussian_preserving':'s','self_masking_logistic_population':'^'}
vals=np.linspace(-.25,.25,6)
condition_offsets={}; k=0
for pv in [20,50]:
    for mode in mode_order:
        condition_offsets[(pv,mode)]=vals[k]; k+=1
fig,axes=plt.subplots(1,2,figsize=(6.0,2.52),sharey=True)
for ti,t in enumerate(top_order):
    ycenter=3-ti
    if ti%2==1:
        for ax in axes: ax.axhspan(ycenter-.43,ycenter+.43,color='#F4F4F1',zorder=0)
    for pv in [20,50]:
        for mode in mode_order:
            r=L[(L.topology==t)&(L.p==pv)&(L.missingness_mode==mode)].iloc[0]
            y=ycenter+condition_offsets[(pv,mode)]
            mk=mode_mk[mode]; c=mode_col[mode]; mfc='white' if pv==20 else c
            axes[0].errorbar(100*r.f1_delta_local_minus_global_mean,y,
                xerr=[[100*(r.f1_delta_local_minus_global_mean-r.f1_delta_local_minus_global_lo95)],[100*(r.f1_delta_local_minus_global_hi95-r.f1_delta_local_minus_global_mean)]],
                fmt=mk,ms=5.4,capsize=1.8,color=c,mfc=mfc,mec=c,mew=1.0,lw=1.1,zorder=3)
            axes[1].plot(100*r.ci_saving_fraction_batch_targets_mean,y,marker=mk,ms=5.4,color=c,mfc=mfc,mec=c,mew=1.0,ls='none',zorder=3)
axes[0].axvline(0,color='#777C82',ls=(0,(3,2)),lw=.9)
for ax in axes:
    for yy in [.5,1.5,2.5]: ax.axhline(yy,color=HAIR,lw=.65,zorder=1)
    ax.set_yticks([3,2,1,0]); ax.set_yticklabels([top_lab[t] for t in top_order])
    style_axes(ax,ygrid=False,xgrid=True)
axes[0].xaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
axes[1].xaxis.set_major_formatter(mpl.ticker.FormatStrFormatter('%.2f'))
axes[0].set_xlabel('Local $-$ global-restriction $F_1$ (pp)')
axes[1].set_xlabel('Batch CI-test saving (%)')
legend_handles=[
    Line2D([0],[0],marker='o',color='none',markerfacecolor=COMPLETE,markeredgecolor=COMPLETE,markersize=5.8,label='Complete'),
    Line2D([0],[0],marker='s',color='none',markerfacecolor=QUAD,markeredgecolor=QUAD,markersize=5.8,label='Quadratic'),
    Line2D([0],[0],marker='^',color='none',markerfacecolor=LOGISTIC,markeredgecolor=LOGISTIC,markersize=5.8,label='Logistic'),
    Line2D([0],[0],marker='o',color=INK,ls='none',markerfacecolor='white',markersize=5.6,label='$p=20$'),
    Line2D([0],[0],marker='o',color=INK,ls='none',markerfacecolor=INK,markersize=5.6,label='$p=50$'),
]
fig.legend(handles=legend_handles,loc='upper center',bbox_to_anchor=(.5,.985),ncol=5,frameon=False,columnspacing=.90,handletextpad=.28,borderaxespad=0,alignment='center')
fig.subplots_adjust(left=.185,right=.995,bottom=.215,top=.80,wspace=.24)
save_figure(fig,'matched_local_comparison')

# ---------------------------------------------------------------------------
# Information-rate figure. The shaded corridor is exactly the region
# between the proved necessary and sufficient formulas, visually emphasizing
# their matching logarithmic graph-size dependence without implying equality.
# ---------------------------------------------------------------------------
ms=np.array([4,8,16,32,64,128,256,512,1024]); b=.5; delta=.05; a_mask=1.0; c_mask=.9; eta=.25
qret=c_mask/math.sqrt(1+a_mask); beff=b/math.sqrt(1+a_mask)
def write_failure(n, m):
    """Write the information-rate failure term used by the reference table."""
    n0=math.floor((1-eta)*n*qret)
    return 2*m*(1+beff**2/4)**(-n0/2)+m*math.exp(-(eta**2)*n*qret/2)
upper=[]; lower=[]
for m in ms:
    n=1
    while write_failure(n,m)>delta: n+=1
    upper.append(n)
    lower.append((2*(1+a_mask)/(qret*b*b))*math.log(m/(4*(-math.log(1-delta)))))
rate=pd.DataFrame({'m':ms,'upper_sufficient_n':upper,'lower_necessary_n':lower,'a':a_mask,'c':c_mask,'pi':qret,'b':b,'delta':delta,'eta':eta}); rate.to_csv(DER/'information_rate_bounds.csv',index=False)
x=np.log2(ms)
upper=np.asarray(upper); lower=np.asarray(lower)
fig,ax=plt.subplots(figsize=(6.0,2.38))
ax.fill_between(x,lower,upper,color='#ECEAE4',alpha=1.0,lw=0,zorder=0)
ax.plot(x,upper,marker='o',color=QUAD,mec='white',mew=.6,zorder=2)
ax.plot(x,lower,marker='s',color=LOGISTIC,mec='white',mew=.6,zorder=2)
ax.set_xticks(x); ax.set_xticklabels([rf'$2^{{{int(v)}}}$' for v in x])
ax.set_xlabel('Independent graph bits $m$')
ax.set_ylabel('Original sample size $n$')
information_rate_handles=[
    Line2D([0],[0],color=QUAD,lw=2.1,marker='o',mec='white',mew=.6,label='Concrete OLS sufficient bound'),
    Line2D([0],[0],color=LOGISTIC,lw=2.1,marker='s',mec='white',mew=.6,label='Any-estimator necessary bound'),
]
fig.legend(handles=information_rate_handles,loc='upper center',bbox_to_anchor=(.5,.985),ncol=2,frameon=False,handlelength=1.65,handletextpad=.45,columnspacing=1.40,borderaxespad=0,alignment='center')
style_axes(ax)
fig.subplots_adjust(left=.105,right=.995,bottom=.245,top=.80)
save_figure(fig,'information_rate')

# ---------------------------------------------------------------------------
# Tables: full-width editorial system. Every numeric/result column is centered,
# while prose columns receive deliberately larger semantic width. The custom
# L{w}/C{w} tabularx column types are defined in main.tex and online_appendix.tex.
# ---------------------------------------------------------------------------
labels={'er_expected_degree_2':r'Erd\H{o}s--R\'enyi','random_regular_d2':'Random regular','small_world_k2':'Small world','scale_free_m2':'Scale free'}

# Depth scope table
DS=depth.groupby('topology').agg(total=('seed','size'),covered=('oracle_search_depth_premise_satisfied','sum')).reset_index()
DS['topology']=pd.Categorical(DS['topology'], categories=['er_expected_degree_2','random_regular_d2','small_world_k2','scale_free_m2'], ordered=True)
DS=DS.sort_values('topology')
with open(TAB/'search_depth_scope.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.13}
\setlength{\tabcolsep}{5pt}
\begin{tabularx}{\textwidth}{@{}L{1.25}C{0.72}C{0.72}L{1.31}@{}}
\toprule
Topology & Covered & Total & Interpretation \\
\midrule
''')
    roles={'er_expected_degree_2':'boundary regime','random_regular_d2':'theorem-aligned','small_world_k2':'theorem-aligned','scale_free_m2':'depth stress'}
    for _,r in DS.iterrows(): write_latex_row(f, f"{labels[r.topology]} & {int(r.covered)} & {int(r.total)} & {roles[r.topology]}")
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Depth-$3$ separator coverage used to distinguish theorem-aligned and stress regimes. For each structure, every nonedge was checked exhaustively for a separating set of size at most three within the candidate pool; a failed structure retains a concrete unresolved-nonedge witness.}
\label{tab:depth-scope}
\end{table}
''')

# Empirical study / Monte Carlo precision table
primary_base_gate=gates[gates.block=='primary_scaling_10_seeds'].iloc[0]
primary_comb_gate=gates[gates.block=='primary_scaling_20_seeds'].iloc[0]
alpha_gate=gates[gates.block=='significance_threshold_sensitivity'].iloc[0]
ret_gate=gates[gates.block=='retention_sensitivity'].iloc[0]
local_paired_max=float(local['f1_delta_local_minus_global_halfwidth95'].max())
with open(TAB/'experiment_program.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.13}
\setlength{\tabcolsep}{4pt}
\begin{tabularx}{\textwidth}{@{}L{1.38}C{0.72}C{0.58}C{0.82}C{0.78}C{0.72}@{}}
\toprule
Experiment & Runs & Seeds & Groups & $h>0.05$ & Max. $h$ \\
\midrule
''')
    write_latex_row(f, f"Main scaling (10 seeds) & 1020 & 10 & {int(primary_base_gate.groups)} & {int(primary_base_gate.groups_over_005)}/{int(primary_base_gate.groups)} & {primary_base_gate.max_f1_halfwidth95:.2f}")
    write_latex_row(f, f"Main scaling (20 seeds) & 2040 & 20 & {int(primary_comb_gate.groups)} & 0/{int(primary_comb_gate.groups)} & {primary_comb_gate.max_f1_halfwidth95:.2f}")
    write_latex_row(f, f"Significance schedule & 360 & 10 & {int(alpha_gate.groups)} & 0/{int(alpha_gate.groups)} & {alpha_gate.max_f1_halfwidth95:.2f}")
    write_latex_row(f, f"Retention & 120 & 10 & {int(ret_gate.groups)} & 0/{int(ret_gate.groups)} & {ret_gate.max_f1_halfwidth95:.2f}")
    write_latex_row(f, f"Dedicated local & 240 & 10 & 24 paired & 0/24 & {local_paired_max:.2f}")
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Empirical study size and Monte Carlo precision, where $h$ is the Student-$t$ 95\% $F_1$ half-width. A prespecified precision rule extended the main scaling experiment uniformly from 10 to 20 graph seeds after six groups exceeded $h=0.05$ in the 10-seed analysis; the extension was applied to every main-scaling condition. The 20-seed summaries are descriptive, while paired inferential contrasts retain the 10-seed design.}
\label{tab:evidence-program}
\end{table}
''')

# Sample-growth schedule + paired contrast summary as two aligned full-width blocks.
gamma_rows=paired10[paired10.contrast=='gamma_1.25_minus_1.0'].copy(); gamma_above=gamma_rows[gamma_rows.p>50]
def count_significant_groups(df, col):
    """Count paired intervals wholly above, below, or overlapping zero."""
    pos=int((df[f'{col}_delta_lo95']>0).sum()); neg=int((df[f'{col}_delta_hi95']<0).sum()); return pos,neg,len(df)-pos-neg
primary_config = yaml.safe_load((ROOT/'configs'/'primary_scaling.yaml').read_text())
reference_p = int(primary_config['base']['reference_p'])
reference_n_over_p = float(primary_config['base']['reference_n_over_p'])
schedule=[]
for pv in [20,50,75,100,150]:
    n1 = calibrated_sample_size(pv, 1.0, reference_p, reference_n_over_p)
    n125 = calibrated_sample_size(pv, 1.25, reference_p, reference_n_over_p)
    schedule.append((pv,n1,n125))
with open(TAB/'sample_growth.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.12}
\setlength{\tabcolsep}{4pt}
\begin{tabularx}{\textwidth}{@{}C{0.62}C{1.02}C{1.13}C{0.98}C{1.25}@{}}
\toprule
$p$ & $n$ ($\gamma=1$) & $n$ ($\gamma=1.25$) & $\Delta n$ & Relative change \\
\midrule
''')
    for pv,n1,n125 in schedule:
        rel=100*(n125-n1)/n1
        write_latex_row(f, f'{pv} & {n1} & {n125} & {n125-n1:+d} & {rel:+.2f}\\%')
    f.write(r'''\midrule
\multicolumn{5}{@{}l}{\textit{Paired graph-recovery effects for $p>50$}} \\
Metric & Mean change (pp) & CI $>0$ & CI $<0$ & CI includes $0$ \\
\cmidrule(lr){1-5}
''')
    for col,lab in [('f1','$F_1$'),('precision','Precision'),('recall','Recall')]:
        po,ne,ov=count_significant_groups(gamma_above,col); mean=100*gamma_above[f'{col}_delta_mean'].mean()
        write_latex_row(f, f'{lab} & {mean:+.2f} & {po} & {ne} & {ov}')
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Sample-size schedules and paired finite-grid effects. The upper five rows give the two schedules, which coincide at $p=50$; hence $\gamma=1.25$ uses fewer samples below the anchor and more above it. The lower three rows summarize paired 10-seed graph-recovery changes for $p>50$ across global and target-restriction evaluations; interval counts refer to 95\% paired intervals. The comparison is finite-sample and is not used to fit an asymptotic exponent.}
\label{tab:growth-summary}
\end{table}
''')

# Retention summary table
ret_global=ret[ret.evaluation_scope=='global_whole_skeleton'].copy()
ret_by=ret_global.groupby('missing_rate_target').agg(f1=('f1_mean','mean'),precision=('precision_mean','mean'),recall=('recall_mean','mean'),eff=('trace_ci_effective_fraction_mean_mean','mean')).reset_index()
with open(TAB/'retention_sensitivity.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.13}
\setlength{\tabcolsep}{5pt}
\begin{tabularx}{\textwidth}{@{}C{1.00}C{1.00}C{1.00}C{1.00}C{1.00}@{}}
\toprule
Missingness & Precision (\%) & Recall (\%) & $F_1$ (\%) & Usable records (\%) \\
\midrule
''')
    for _,r0 in ret_by.iterrows(): write_latex_row(f, f"{100*r0.missing_rate_target:.0f}\\% & {100*r0.precision:.2f} & {100*r0.recall:.2f} & {100*r0.f1:.2f} & {100*r0.eff:.2f}")
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Quadratic-mask retention sensitivity, averaged over the global random-regular and small-world conditions at $p\in\{50,100\}$. The usable-record fraction decreases monotonically with requested missingness, whereas $F_1$ does not.}
\label{tab:retention-summary}
\end{table}
''')

# Population-margin boundary table
covered=margins[margins.depth_ok.astype(bool)].copy()
with open(TAB/'population_margin_diagnostics.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.13}
\setlength{\tabcolsep}{5pt}
\begin{tabularx}{\textwidth}{@{}L{1.55}C{0.72}C{0.73}@{}}
\toprule
Diagnostic over depth-covered structures & Complete law & Selected quadratic law \\
\midrule
''')
    write_latex_row(f, f"Minimum true-edge query $|\\rho|$ & ${format_scientific_tex(covered.oracle_edge_partial_corr_min.min())}$ & ${format_scientific_tex(covered.selected_edge_partial_corr_min.min())}$")
    write_latex_row(f, f"Structures with minimum $|\\rho|<0.01$ & {int((covered.oracle_edge_partial_corr_min<.01).sum())}/134 & {int((covered.selected_edge_partial_corr_min<.01).sum())}/134")
    write_latex_row(f, f"Minimum query-retention diagnostic (\\%) & -- & {100*covered.selected_edge_query_retention_min.min():.2f}")
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Finite-grid population-margin diagnostics on the 134 structures satisfying the depth-$3$ search premise. These values characterize the simulated grid and are not interpreted as a dimension-uniform strong-faithfulness theorem.}
\label{tab:margin-boundary}
\end{table}
''')

# Alpha summary table
fa=alpha[alpha.contrast=='fixed_005_minus_n_inverse_half']
def count_contrast_signs(df, col):
    """Count the signs of paired contrast intervals for a reported metric."""
    pos=(df[f'{col}_delta_lo95']>0).sum(); neg=(df[f'{col}_delta_hi95']<0).sum(); return int(pos),int(neg),int(len(df)-pos-neg)
with open(TAB/'threshold_sensitivity.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.13}
\setlength{\tabcolsep}{5pt}
\begin{tabularx}{\textwidth}{@{}L{1.65}C{0.95}C{0.80}C{0.80}C{0.80}@{}}
\toprule
Metric & Mean change & CI $>0$ & CI $<0$ & CI includes $0$ \\
\midrule
''')
    for col,lab in [('f1','$F_1$ (pp)'),('precision','Precision (pp)'),('recall','Recall (pp)'),('fp','False positives'),('trace_ci_tests','CI tests')]:
        po,ne,ov=count_contrast_signs(fa,col); mean=fa[f'{col}_delta_mean'].mean(); shown=100*mean if col in {'f1','precision','recall'} else mean
        write_latex_row(f, f"{lab} & {shown:.2f} & {po} & {ne} & {ov}")
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Paired contrasts for fixed $0.05$ minus the practical $n^{-1/2}$ schedule across 36 matched conditions. The last three columns count 95\% paired intervals lying wholly above zero, wholly below zero, or including zero. The practical $n^{-1/2}$ schedule is an empirical design choice, not the margin-dependent Kalisch--B\"uhlmann significance sequence \citep{kalisch2007estimating}.}
\label{tab:alpha-summary}
\end{table}
''')

# Local summary table with grouped headers
agg=[]
for topo in ['er_expected_degree_2','random_regular_d2','small_world_k2','scale_free_m2']:
    g=local[local.topology==topo]
    pos=(g.f1_delta_local_minus_global_lo95>0).sum(); neg=(g.f1_delta_local_minus_global_hi95<0).sum(); ov=len(g)-pos-neg
    agg.append((labels[topo] if topo in labels else topo,pos,neg,ov,g.ci_saving_fraction_batch_targets_mean.min(),g.ci_saving_fraction_batch_targets_mean.max()))
with open(TAB/'matched_local.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.13}
\setlength{\tabcolsep}{4pt}
\begin{tabularx}{\textwidth}{@{}L{1.35}C{0.93}C{0.93}C{0.93}C{0.93}C{0.93}@{}}
\toprule
& \multicolumn{3}{c}{Paired local-minus-global $F_1$ interval} & \multicolumn{2}{c}{Batch CI-test saving} \\
\cmidrule(lr){2-4}\cmidrule(l){5-6}
Topology & CI $>0$ & CI $<0$ & Includes $0$ & Minimum & Maximum \\
\midrule
''')
    for a0,pos,neg,ov,mn,mx in agg: write_latex_row(f, f"{a0} & {pos} & {neg} & {ov} & {100*mn:.2f}\\% & {100*mx:.2f}\\%")
    f.write(r'''\bottomrule
\end{tabularx}
\caption{Matched dedicated-local validation on identical targets, graphs, and samples. Savings compare processing the selected targets locally with one global fit. CI-test savings are positive in all 24 conditions, while the $F_1$ difference depends on topology and observation regime.}
\label{tab:local-summary}
\end{table}
''')

# Information-rate symbolic summary table
with open(TAB/'information_rate.tex','w') as f:
    f.write(r'''\begin{table}[t]
\centering
\small
\renewcommand{\arraystretch}{1.16}
\setlength{\tabcolsep}{6pt}
\begin{tabularx}{\textwidth}{@{}L{0.72}C{1.28}@{}}
\toprule
Quantity & Exact expression in the self-masked pair family \\
\midrule
Parent retention & $\pi=c/\sqrt{1+a}$ \\
Selected parent variance & $1/(1+a)$ \\
Effective retained signal & $b_{\rm eff}=b/\sqrt{1+a}$ \\
One-record observed KL & $\pi b^2/[2(1+a)]$ \\
Concrete failure bound & $2m(1+b_{\rm eff}^2/4)^{-n_0/2}+m\exp(-\eta^2n\pi/2)$ \\
Necessary $n$ & $\frac{2(1+a)}{\pi b^2}\log\!\frac{m}{4[-\log(1-\delta)]}$ \\
\bottomrule
\end{tabularx}
\caption{Self-masked sparse-pair calibration. The exact expressions retain the masking dependence; the $\Theta(b^{-2}\log(m/\delta))$ shorthand applies only after fixing the positive masking parameters.}
\label{tab:information-rate-summary}
\end{table}
''')

pd.DataFrame(GEOMETRY).to_csv(DER/'figure_axis_geometry.csv',index=False)
print('Generated figures:', sorted(p.name for p in FIG.glob('*.pdf')))
print('Generated tables:', sorted(p.name for p in TAB.glob('*.tex')))
