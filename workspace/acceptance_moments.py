"""Generate exact, kernel checked polynomial sum proofs (no evaluated large sums)."""
from pathlib import Path
from math import comb
R='(N:ℝ)'
S=[R, f'{R}*({R}-1)/2', f'{R}*({R}-1)*(2*{R}-1)/6',
   f'{R}^2*({R}-1)^2/4', f'{R}*({R}-1)*(2*{R}-1)*(3*{R}^2-3*{R}-1)/30',
   f'{R}^2*({R}-1)^2*(2*{R}^2-2*{R}-1)/12',
   f'{R}*({R}-1)*(2*{R}-1)*(3*{R}^4-6*{R}^3+3*{R}+1)/42']

def poly(coeff, x):
    return ' + '.join(f'({c})*{x}^{p}' if p else f'({c})' for p,c in reversed(list(enumerate(coeff))))

def args(coeff): return ' '.join(f'({x})' for x in coeff)

s='''namespace ShorECDLP.Acceptance
open scoped BigOperators
noncomputable section
'''
for p in range(7):
    s+=f'''\nlemma power_sum_{p} (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^{p} = {S[p]} := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
'''
coeff=[f'a{p}' for p in range(7)]
s+=f'''\nlemma sum_poly_six (N : ℕ) {' '.join(f'({c} : ℝ)' for c in coeff)} :
    ∑ x ∈ Finset.range N, ({poly(coeff,'(x:ℝ)')}) =
      {' + '.join(f'{c}*({S[p]})' for p,c in reversed(list(enumerate(coeff))))} := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, {', '.join(f'power_sum_{p}' for p in range(1,7))},
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring
'''
D={2:f'{R}^2*({R}^2-1)/6',4:f'{R}^2*({R}^2-1)*(2*{R}^2-3)/30',6:f'{R}^2*({R}^2-1)*(3*{R}^4-11*{R}^2+10)/84'}
for p in [4,6]:
    inn=[str(comb(p,j)*(-1)**j)+f'*(x:ℝ)^{p-j}' if j<=p else '0' for j in range(7)]
    out=[str(comb(p,j)*(-1)**(p-j))+f'*({S[p-j]})' if j<=p else '0' for j in range(7)]
    s+=f'''\nlemma difference_sum_{p} (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^{p} = {D[p]} := by
  have hi (x : ℕ) : (∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^{p}) = {poly(out,'(x:ℝ)')} := by
    calc
      _ = ∑ y ∈ Finset.range N, ({poly(inn,'(y:ℝ)')}) := by
        apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [sum_poly_six]; ring
  simp_rw [hi]
  rw [sum_poly_six]
  ring
'''
C={4:'(r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240',6:'(r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344'}
for p in [4,6]:
    coeff=[str(comb(p,j))+f'*(-(r/2:ℕ):ℝ)^{p-j}' if j<=p else '0' for j in range(7)]
    s+=f'''\nlemma centered_{p} (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^{p} = {C[p]} := by
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^{p}) r]
  trans ∑ x ∈ Finset.range r, ({poly(coeff,'(x:ℝ)')})
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_poly_six]
    have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
      exact_mod_cast (by omega : r = 2*(r/2)+1)
    rw [he]
    ring
'''
s+='\nend\nend ShorECDLP.Acceptance\n'
Path('workspace/AcceptanceMoments.lean').write_text(s)
