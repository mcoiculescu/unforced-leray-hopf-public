import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11

/-!
# `PartIII-b:C/inst/11/1`: support of `ĥ_A` (hAcoef) for `s > 1.1/ν`

Source `the November 2 reference manuscript` 4953-4955 (`χ_f(s) = χ̂_f(νs) = 0`
for `νs ≥ 1.1`), 4979-4980 (`ĥ_A`), 5063-5079.  On `s > 1.1/ν` the cutoff vanishes, so
`A^y = 0` at `s`, the lattice sums `h^p_A`, `ψ^p_A` and `𝒦ψ^p_A` vanish, hence `ĥ_A = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hAc_ay_zero (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (s : ℝ) (hs : (11 / 10) / ν < s) : Ay ν χf A s = 0 := by
  have ht : 11 / 10 ≤ ν * s := by
    rw [div_lt_iff₀ hν] at hs
    nlinarith
  unfold Ay
  rw [hχ.zero (ν * s) ht, zero_smul]

theorem hAc_merApply_zero (y : ℝ × ℝ) : merApply (0 : Mat3) y = 0 := by
  ext <;> simp [merApply]

theorem hAc_emb_zero : emb 0 = 0 := by
  funext i
  fin_cases i <;> simp [emb]

theorem hAc_hpA_zero (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (h : Ay ν χ A s = 0) : hpA ν χ A s x = 0 := by
  unfold hpA
  simp only [h, hAc_merApply_zero, map_zero, sub_zero, tsum_zero]

theorem hAc_psipA_zero (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (h : Ay ν χ A s = 0) : psipA ν χ A s x = 0 := by
  have hT : merTrace (0 : Mat3) = 0 := by simp [merTrace]
  unfold psipA
  simp only [h, hT, zero_mul, hAc_merApply_zero, map_zero, sub_zero, tsum_zero]

theorem hAc_kop_zero (χf : ℝ → ℝ) (ν : ℝ) (A : ℝ → Mat3) (T s : ℝ) (hs : T < s) (x : ℝ × ℝ)
    (hz : ∀ s' : ℝ, T < s' → ∀ y : ℝ × ℝ, psipA ν χf A s' y = 0) :
    Kop (fun s' y => psipA ν χf A s' y) s x = 0 := by
  have hfun : (fun y => psipA ν χf A s y) = fun _ => (0 : ℝ) := funext fun y => hz s hs y
  have hev : (fun s' => psipA ν χf A s' x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs) fun s' hs' => hz s' hs' x
  show x.2 * fderiv ℝ (fun y => psipA ν χf A s y) x (ei 1)
      + 2 * s * deriv (fun s' => psipA ν χf A s' x) s = 0
  rw [hfun, hev.deriv_eq]
  simp

theorem hAc_hhat_zero (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hp : hpA ν χf A s x = 0) (hq : psipA ν χf A s x = 0)
    (hk : Kop (fun s' y => psipA ν χf A s' y) s x = 0) :
    hhatA ν ε χf A s x = 0 := by
  unfold hhatA
  rw [hp, hq, hk]
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, mul_zero, add_zero, Prod.mk_zero_zero,
    hAc_emb_zero, smul_zero]

theorem hAcSupport (χf : ℝ → ℝ) : HAcSupport χf := by
  unfold HAcSupport
  intro hχ ν ε hν A s hs x
  have hz : ∀ s' : ℝ, (11 / 10) / ν < s' → ∀ y : ℝ × ℝ, psipA ν χf A s' y = 0 :=
    fun s' hs' y => hAc_psipA_zero ν χf A s' y (hAc_ay_zero χf hχ ν hν A s' hs')
  have hh := hAc_hhat_zero ν ε χf A s x
    (hAc_hpA_zero ν χf A s x (hAc_ay_zero χf hχ ν hν A s hs))
    (hAc_psipA_zero ν χf A s x (hAc_ay_zero χf hχ ν hν A s hs))
    (hAc_kop_zero χf ν A ((11 / 10) / ν) s hs x hz)
  show merOf ((Real.sqrt s)⁻¹ • hhatA ν ε χf A s x) = 0
  rw [hh, smul_zero]
  ext i
  fin_cases i <;> simp [merOf]

end UnforcedLeray.Short.PartIIIb.Concrete
