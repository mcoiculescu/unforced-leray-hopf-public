import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefLinear

/-!
# `PartIII-b:C/grad/3/4/1/4`: chain rule `GradEntryChain`

Proves `gradEntryChain : GradEntryChain`: the entries of `s⁻¹∇ĥ_A` are built from the
chart derivatives of `√s·b_r` and `√s·b_z` (source 4980, 5036-5039), with
`b_z = h^p_z + ε(ψ^p − 𝒦ψ^p)`, and `𝒦(√s b) = √s(𝒦b + b)`.
Chain rule only (no lattice estimates): the three leaves enter as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `b_z = h^p_z + ε(ψ^p_A − 𝒦ψ^p_A)` (source 4980). -/
def bzF (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → ℝ × ℝ → ℝ :=
  fun s' y => hpZ ν χ A s' y + ε * (psipA ν χ A s' y - Kop (psipA ν χ A) s' y)

theorem ge_dQ_add (f g : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (f s) x) (hg : DifferentiableAt ℝ (g s) x) :
    dQ (fun s' y => f s' y + g s' y) s x = dQ f s x + dQ g s x := by
  simp only [dQ]
  rw [show (fun y => f s y + g s y) = f s + g s from rfl, fderiv_add hf hg]
  simp

theorem ge_dEta_add (f g : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (f s) x) (hg : DifferentiableAt ℝ (g s) x) :
    dEta (fun s' y => f s' y + g s' y) s x = dEta f s x + dEta g s x := by
  simp only [dEta]
  rw [show (fun y => f s y + g s y) = f s + g s from rfl, fderiv_add hf hg]
  simp

theorem ge_dQ_sub (f g : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (f s) x) (hg : DifferentiableAt ℝ (g s) x) :
    dQ (fun s' y => f s' y - g s' y) s x = dQ f s x - dQ g s x := by
  simp only [dQ]
  rw [show (fun y => f s y - g s y) = f s - g s from rfl, fderiv_sub hf hg]
  simp

theorem ge_dEta_sub (f g : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (f s) x) (hg : DifferentiableAt ℝ (g s) x) :
    dEta (fun s' y => f s' y - g s' y) s x = dEta f s x - dEta g s x := by
  simp only [dEta]
  rw [show (fun y => f s y - g s y) = f s - g s from rfl, fderiv_sub hf hg]
  simp

theorem ge_dQ_cmul (c : ℝ) (f : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (f s) x) :
    dQ (fun s' y => c * f s' y) s x = c * dQ f s x := by
  simp only [dQ]
  rw [fderiv_const_mul hf c]
  simp

theorem ge_dEta_cmul (c : ℝ) (f : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (f s) x) :
    dEta (fun s' y => c * f s' y) s x = c * dEta f s x := by
  simp only [dEta]
  rw [fderiv_const_mul hf c]
  simp

/-- `Kop` of a `√s`-weighted function: `𝒦(√s b) = √s(𝒦b + b)`. -/
theorem ge_kop_sqrt (b : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) (hs : 0 < s)
    (h1 : DifferentiableAt ℝ (b s) x) (h1' : DifferentiableAt ℝ (fun s' => b s' x) s) :
    Kop (fun s' y => Real.sqrt s' * b s' y) s x = Real.sqrt s * (Kop b s x + b s x) := by
  have hsq : HasDerivAt (fun s' => Real.sqrt s') (1 / (2 * Real.sqrt s)) s :=
    Real.hasDerivAt_sqrt hs.ne'
  have hprod : HasDerivAt (fun s' => Real.sqrt s' * b s' x)
      (1 / (2 * Real.sqrt s) * b s x + Real.sqrt s * deriv (fun s' => b s' x) s) s :=
    hsq.mul h1'.hasDerivAt
  have hF : fderiv ℝ (fun y => Real.sqrt s * b s y) x = Real.sqrt s • fderiv ℝ (b s) x :=
    fderiv_const_mul h1 _
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have h2 : (2 * Real.sqrt s) ≠ 0 := by
    have : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    positivity
  have key : 2 * s * (1 / (2 * Real.sqrt s)) = Real.sqrt s := by
    rw [mul_one_div, div_eq_iff h2]
    linear_combination (-2 : ℝ) * hss
  show x.2 * fderiv ℝ (fun y => Real.sqrt s * b s y) x (ei 1)
      + 2 * s * deriv (fun s' => Real.sqrt s' * b s' x) s
      = Real.sqrt s * (Kop b s x + b s x)
  rw [hF, hprod.deriv]
  unfold Kop
  simp only [smul_apply, smul_eq_mul]
  linear_combination (b s x) * key

theorem ge_physDr (ε : ℝ) (b : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) (hs : 0 < s)
    (h1 : DifferentiableAt ℝ (b s) x) (h1' : DifferentiableAt ℝ (fun s' => b s' x) s) :
    physDr ε (fun s' y => Real.sqrt s' * b s' y) s x
      = s * (dQ b s x - ε * (Kop b s x + b s x)) := by
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hQ : dQ (fun s' y => Real.sqrt s' * b s' y) s x = Real.sqrt s * dQ b s x := by
    simp only [dQ]
    rw [fderiv_const_mul h1]
    simp
  unfold physDr
  rw [hQ, ge_kop_sqrt b s x hs h1 h1']
  linear_combination (dQ b s x - ε * (Kop b s x + b s x)) * hss

theorem ge_physDz (b : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) (hs : 0 < s)
    (h1 : DifferentiableAt ℝ (b s) x) :
    physDz (fun s' y => Real.sqrt s' * b s' y) s x = s * dEta b s x := by
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hE : dEta (fun s' y => Real.sqrt s' * b s' y) s x = Real.sqrt s * dEta b s x := by
    simp only [dEta]
    rw [fderiv_const_mul h1]
    simp
  unfold physDz
  rw [hE]
  linear_combination (dEta b s x) * hss

theorem ge_abs_eps {ε t T : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ 1) (ht : |t| ≤ T) (hT : 0 ≤ T) :
    |ε * t| ≤ T := by
  rw [abs_mul, abs_of_nonneg h0]
  nlinarith [abs_nonneg t]

theorem ge_abs_add {a b U V : ℝ} (ha : |a| ≤ U) (hb : |b| ≤ V) : |a + b| ≤ U + V := by
  rw [abs_le] at *
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem ge_abs_sub {a b U V : ℝ} (ha : |a| ≤ U) (hb : |b| ≤ V) : |a - b| ≤ U + V := by
  rw [abs_le] at *
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem ge_hhatA0 (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hhatA ν ε χ A s x 0 = Real.sqrt s * hpR ν χ A s x := by
  simp [hhatA, emb, hpR]

theorem ge_chart0 (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) :
    chartComp (hhatA ν ε χ A) 0 = fun s' y => Real.sqrt s' * hpR ν χ A s' y := by
  funext s' y
  exact ge_hhatA0 ν ε χ A s' y

theorem ge_chart2 (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) :
    chartComp (hhatA ν ε χ A) 2 = fun s' y => Real.sqrt s' * bzF ν ε χ A s' y := by
  funext s' y
  simp [chartComp, hhatA, emb, bzF, hpZ]

theorem gradEntryChain : GradEntryChain := by
  intro hHp hPsi hSm
  obtain ⟨Ch, hCh, hH⟩ := hHp
  obtain ⟨Cp, hCp, hP⟩ := hPsi
  refine ⟨12 * (Ch + Cp), mul_nonneg (by norm_num) (add_nonneg hCh hCp), ?_⟩
  intro ν ε s χf A hd hε0 hε1 x i j
  have hd' := hd
  unfold GradData at hd'
  obtain ⟨hν, hν1, hs, hsT, hA⟩ := hd'
  have hs0 : s ≠ 0 := hs.ne'
  have hgF : 0 ≤ gradF ν χf A s := by
    unfold gradF frob
    positivity
  have hLS : 0 ≤ latticeS gradAlpha gradK (cOf ν) x := by
    unfold latticeS
    exact tsum_nonneg fun j => by unfold latticeW; positivity
  have hT : 0 ≤ gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x := mul_nonneg hgF hLS
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = (Ch + Cp) * (gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x) :=
    ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by
    rw [hUdef]
    exact mul_nonneg (by linarith) hT
  have toU : ∀ p : ℝ, |p| ≤ Ch * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x → |p| ≤ U := by
    intro p h
    rw [hUdef]
    calc |p| ≤ Ch * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x := h
      _ = Ch * (gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x) := by ring
      _ ≤ (Ch + Cp) * (gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x) :=
          mul_le_mul_of_nonneg_right (by linarith) hT
  have toU' : ∀ p : ℝ, |p| ≤ Cp * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x → |p| ≤ U := by
    intro p h
    rw [hUdef]
    calc |p| ≤ Cp * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x := h
      _ = Cp * (gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x) := by ring
      _ ≤ (Ch + Cp) * (gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x) :=
          mul_le_mul_of_nonneg_right (by linarith) hT
  have hfin : 12 * (Ch + Cp) * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x = 12 * U := by
    rw [hUdef]; ring
  -- envelopes of h^p_{r,z} and ψ^p_A
  obtain ⟨hR0, hRq, hRe, hRK⟩ := hH ν s χf A hd x (hpR ν χf A) (Or.inl rfl)
  obtain ⟨hZ0, hZq, hZe, hZK⟩ := hH ν s χf A hd x (hpZ ν χf A) (Or.inr rfl)
  obtain ⟨hP0, hPq, hPe, hPK, hPKq, hPKe, hPKK⟩ := hP ν s χf A hd x
  have hr0 : |hpR ν χf A s x| ≤ U := toU _ hR0
  have hrq : |dQ (hpR ν χf A) s x| ≤ U := toU _ hRq
  have hre : |dEta (hpR ν χf A) s x| ≤ U := toU _ hRe
  have hrK : |Kop (hpR ν χf A) s x| ≤ U := toU _ hRK
  have hz0 : |hpZ ν χf A s x| ≤ U := toU _ hZ0
  have hzq : |dQ (hpZ ν χf A) s x| ≤ U := toU _ hZq
  have hze : |dEta (hpZ ν χf A) s x| ≤ U := toU _ hZe
  have hzK : |Kop (hpZ ν χf A) s x| ≤ U := toU _ hZK
  have hp0 : |psipA ν χf A s x| ≤ U := toU' _ hP0
  have hpq : |dQ (psipA ν χf A) s x| ≤ U := toU' _ hPq
  have hpe : |dEta (psipA ν χf A) s x| ≤ U := toU' _ hPe
  have hpK : |Kop (psipA ν χf A) s x| ≤ U := toU' _ hPK
  have hpKq : |dQ (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤ U := toU' _ hPKq
  have hpKe : |dEta (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤ U := toU' _ hPKe
  have hpKK : |Kop (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤ U := toU' _ hPKK
  -- differentiability
  obtain ⟨hR1, hR2⟩ := hSm ν s χf A hd x (hpR ν χf A) (Or.inl rfl)
  obtain ⟨hZ1, hZ2⟩ := hSm ν s χf A hd x (hpZ ν χf A) (Or.inr (Or.inl rfl))
  obtain ⟨hP1, hP2⟩ := hSm ν s χf A hd x (psipA ν χf A) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hK1, hK2⟩ := hSm ν s χf A hd x (fun s' y => Kop (psipA ν χf A) s' y)
    (Or.inr (Or.inr (Or.inr rfl)))
  have hbz1 : DifferentiableAt ℝ (bzF ν ε χf A s) x :=
    hZ1.add ((hP1.sub hK1).const_mul ε)
  have hbz2 : DifferentiableAt ℝ (fun s' => bzF ν ε χf A s' x) s :=
    hZ2.add ((hP2.sub hK2).const_mul ε)
  -- derivative identities for b_z
  have dQbz : dQ (bzF ν ε χf A) s x = dQ (hpZ ν χf A) s x
      + ε * (dQ (psipA ν χf A) s x - dQ (fun s' y => Kop (psipA ν χf A) s' y) s x) := by
    have e1 := ge_dQ_add (hpZ ν χf A) (fun s' y => ε * (psipA ν χf A s' y - Kop (psipA ν χf A) s' y))
      s x hZ1 ((hP1.sub hK1).const_mul ε)
    have e2 := ge_dQ_cmul ε (fun s' y => psipA ν χf A s' y - Kop (psipA ν χf A) s' y) s x
      (hP1.sub hK1)
    have e3 := ge_dQ_sub (psipA ν χf A) (fun s' y => Kop (psipA ν χf A) s' y) s x hP1 hK1
    rw [show dQ (bzF ν ε χf A) s x = dQ (fun s' y => hpZ ν χf A s' y
      + ε * (psipA ν χf A s' y - Kop (psipA ν χf A) s' y)) s x from rfl, e1, e2, e3]
  have dEtabz : dEta (bzF ν ε χf A) s x = dEta (hpZ ν χf A) s x
      + ε * (dEta (psipA ν χf A) s x - dEta (fun s' y => Kop (psipA ν χf A) s' y) s x) := by
    have e1 := ge_dEta_add (hpZ ν χf A) (fun s' y => ε * (psipA ν χf A s' y - Kop (psipA ν χf A) s' y))
      s x hZ1 ((hP1.sub hK1).const_mul ε)
    have e2 := ge_dEta_cmul ε (fun s' y => psipA ν χf A s' y - Kop (psipA ν χf A) s' y) s x
      (hP1.sub hK1)
    have e3 := ge_dEta_sub (psipA ν χf A) (fun s' y => Kop (psipA ν χf A) s' y) s x hP1 hK1
    rw [show dEta (bzF ν ε χf A) s x = dEta (fun s' y => hpZ ν χf A s' y
      + ε * (psipA ν χf A s' y - Kop (psipA ν χf A) s' y)) s x from rfl, e1, e2, e3]
  have kbz : Kop (bzF ν ε χf A) s x = Kop (hpZ ν χf A) s x
      + ε * (Kop (psipA ν χf A) s x + (-1) * Kop (fun s' y => Kop (psipA ν χf A) s' y) s x) := by
    have a1 := kop_add_gen (bzF ν ε χf A) (hpZ ν χf A)
      (fun s' y => ε * (psipA ν χf A s' y - Kop (psipA ν χf A) s' y)) s x hs (fun _ _ _ => rfl)
      hZ1 ((hP1.sub hK1).const_mul ε) hZ2 ((hP2.sub hK2).const_mul ε)
    have a2 := kop_smul_gen (fun s' y => ε * (psipA ν χf A s' y - Kop (psipA ν χf A) s' y))
      (fun s' y => psipA ν χf A s' y - Kop (psipA ν χf A) s' y) ε s x hs (fun _ _ _ => rfl)
      (hP1.sub hK1)
    have a3 := kop_add_gen (fun s' y => psipA ν χf A s' y - Kop (psipA ν χf A) s' y)
      (psipA ν χf A) (fun s' y => (-1) * Kop (psipA ν χf A) s' y) s x hs
      (fun _ _ _ => by ring) hP1 (hK1.const_mul (-1)) hP2 (hK2.const_mul (-1))
    have a4 := kop_smul_gen (fun s' y => (-1) * Kop (psipA ν χf A) s' y)
      (fun s' y => Kop (psipA ν χf A) s' y) (-1) s x hs (fun _ _ _ => rfl) hK1
    rw [a1, a2, a3, a4]
  -- bounds for b_z
  have hneg : |(-1 : ℝ) * Kop (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤ U := by
    rw [abs_mul]
    simpa using hpKK
  have bz0 : |bzF ν ε χf A s x| ≤ 3 * U := by
    show |hpZ ν χf A s x + ε * (psipA ν χf A s x - Kop (psipA ν χf A) s x)| ≤ 3 * U
    have h1 := ge_abs_sub hp0 hpK
    have h2 := ge_abs_eps hε0.le hε1 h1 (by linarith : (0 : ℝ) ≤ U + U)
    have h3 := ge_abs_add hz0 h2
    linarith
  have bzq : |dQ (bzF ν ε χf A) s x| ≤ 3 * U := by
    rw [dQbz]
    have h1 := ge_abs_sub hpq hpKq
    have h2 := ge_abs_eps hε0.le hε1 h1 (by linarith : (0 : ℝ) ≤ U + U)
    have h3 := ge_abs_add hzq h2
    linarith
  have bze : |dEta (bzF ν ε χf A) s x| ≤ 3 * U := by
    rw [dEtabz]
    have h1 := ge_abs_sub hpe hpKe
    have h2 := ge_abs_eps hε0.le hε1 h1 (by linarith : (0 : ℝ) ≤ U + U)
    have h3 := ge_abs_add hze h2
    linarith
  have bzK : |Kop (bzF ν ε χf A) s x| ≤ 3 * U := by
    rw [kbz]
    have h1 := ge_abs_add hpK hneg
    have h2 := ge_abs_eps hε0.le hε1 h1 (by linarith : (0 : ℝ) ≤ U + U)
    have h3 := ge_abs_add hzK h2
    linarith
  -- entries of s⁻¹∇ĥ_A
  have eq00 : s⁻¹ * physGradA ν ε χf A s x 0 0
      = dQ (hpR ν χf A) s x - ε * (Kop (hpR ν χf A) s x + hpR ν χf A s x) := by
    show s⁻¹ * physDr ε (chartComp (hhatA ν ε χf A) 0) s x = _
    rw [ge_chart0, ge_physDr ε (hpR ν χf A) s x hs hR1 hR2, ← mul_assoc, inv_mul_cancel₀ hs0,
      one_mul]
  have eq01 : s⁻¹ * physGradA ν ε χf A s x 0 1 = 0 := by
    show s⁻¹ * (-(ε * Real.sqrt s * hhatA ν ε χf A s x 1)) = 0
    rw [hhatA_phi]
    simp
  have eq02 : s⁻¹ * physGradA ν ε χf A s x 0 2 = dEta (hpR ν χf A) s x := by
    show s⁻¹ * physDz (chartComp (hhatA ν ε χf A) 0) s x = _
    rw [ge_chart0, ge_physDz (hpR ν χf A) s x hs hR1, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have eq10 : s⁻¹ * physGradA ν ε χf A s x 1 0 = 0 := by
    show s⁻¹ * physDr ε (chartComp (hhatA ν ε χf A) 1) s x = 0
    rw [chartComp_hhatA_phi]
    simp [physDr, dQ, Kop]
  have eq11 : s⁻¹ * physGradA ν ε χf A s x 1 1 = ε * hpR ν χf A s x := by
    show s⁻¹ * (ε * Real.sqrt s * hhatA ν ε χf A s x 0) = _
    rw [ge_hhatA0]
    rw [show ε * Real.sqrt s * (Real.sqrt s * hpR ν χf A s x)
        = s * (ε * hpR ν χf A s x) by
          linear_combination (ε * hpR ν χf A s x) * (Real.mul_self_sqrt hs.le),
      ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have eq12 : s⁻¹ * physGradA ν ε χf A s x 1 2 = 0 := by
    show s⁻¹ * physDz (chartComp (hhatA ν ε χf A) 1) s x = 0
    rw [chartComp_hhatA_phi]
    simp [physDz, dEta]
  have eq20 : s⁻¹ * physGradA ν ε χf A s x 2 0
      = dQ (bzF ν ε χf A) s x - ε * (Kop (bzF ν ε χf A) s x + bzF ν ε χf A s x) := by
    show s⁻¹ * physDr ε (chartComp (hhatA ν ε χf A) 2) s x = _
    rw [ge_chart2, ge_physDr ε (bzF ν ε χf A) s x hs hbz1 hbz2, ← mul_assoc, inv_mul_cancel₀ hs0,
      one_mul]
  have eq21 : s⁻¹ * physGradA ν ε χf A s x 2 1 = 0 := by
    show s⁻¹ * (0 : ℝ) = 0
    simp
  have eq22 : s⁻¹ * physGradA ν ε χf A s x 2 2 = dEta (bzF ν ε χf A) s x := by
    show s⁻¹ * physDz (chartComp (hhatA ν ε χf A) 2) s x = _
    rw [ge_chart2, ge_physDz (bzF ν ε χf A) s x hs hbz1, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  -- entry bounds
  have b00 : |dQ (hpR ν χf A) s x - ε * (Kop (hpR ν χf A) s x + hpR ν χf A s x)| ≤ 3 * U := by
    have h1 := ge_abs_add hrK hr0
    have h2 := ge_abs_eps hε0.le hε1 h1 (by linarith : (0 : ℝ) ≤ U + U)
    have h3 := ge_abs_sub hrq h2
    linarith
  have b11 : |ε * hpR ν χf A s x| ≤ U := ge_abs_eps hε0.le hε1 hr0 hU0
  have b20 : |dQ (bzF ν ε χf A) s x - ε * (Kop (bzF ν ε χf A) s x + bzF ν ε χf A s x)| ≤ 9 * U := by
    have h1 := ge_abs_add bzK bz0
    have h2 := ge_abs_eps hε0.le hε1 h1 (by linarith : (0 : ℝ) ≤ 3 * U + 3 * U)
    have h3 := ge_abs_sub bzq h2
    linarith
  rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;>
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
  · rw [eq00]; linarith
  · rw [eq01, abs_zero]; linarith
  · rw [eq02]; linarith
  · rw [eq10, abs_zero]; linarith
  · rw [eq11]; linarith
  · rw [eq12, abs_zero]; linarith
  · rw [eq20]; linarith
  · rw [eq21, abs_zero]; linarith
  · rw [eq22]; linarith

end UnforcedLeray.Short.PartIIIb.Concrete
