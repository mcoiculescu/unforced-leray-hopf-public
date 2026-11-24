import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGSmul
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGOfS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGClm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGSnd
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# `PartIII-b:C/asrc/ra/5/5` : polynomial growth of `PhpA` (source 4741-4745, 4978)

`PhpA ν χ A p = a⁻² • (M_mer (J y) - (k • J y + J v))` with `a = ageA ν s`, `M = A^y(s)`,
`v = M_mer y`, `k = -(⟨y,v⟩/(2a))`.  Written in coordinates the two components are
`a⁻² * I1` and `a⁻² * I2`, where the scalar coefficients are functions of `s` alone
(entries of `A^y = χ(νs) A(s)`, `a⁻²`, `-(2a)⁻¹`) and the factors `y1 = p.2.1`,
`y2 = p.2.2` are polynomial.  The proof closes `PolyGrowth` under sums, products and
negation (the toolkit lemmas of this folder) and under pairing.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phpA_pg_mul (n : ℕ) (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : PolyGrowth n f)
    (hg : PolyGrowth n g) : PolyGrowth n (fun p => f p * g p) :=
  polyGrowth_smul n f g hf hg

theorem phpA_pg_add (n : ℕ) (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : PolyGrowth n f)
    (hg : PolyGrowth n g) : PolyGrowth n (fun p => f p + g p) :=
  (polyGrowth_add n f g hf hg).1

theorem phpA_pg_sub (n : ℕ) (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : PolyGrowth n f)
    (hg : PolyGrowth n g) : PolyGrowth n (fun p => f p - g p) :=
  (polyGrowth_add n f g hf hg).2.1

theorem phpA_pg_neg (n : ℕ) (f : ℝ × (ℝ × ℝ) → ℝ) (hf : PolyGrowth n f) :
    PolyGrowth n (fun p => -f p) :=
  pgAdd_neg n f hf

theorem phpA_pg_pair (n : ℕ) (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : PolyGrowth n f)
    (hg : PolyGrowth n g) : PolyGrowth n (fun p => (f p, g p)) := by
  have h1 := polyGrowth_clm n (ContinuousLinearMap.inl ℝ ℝ ℝ) f hf
  have h2 := polyGrowth_clm n (ContinuousLinearMap.inr ℝ ℝ ℝ) g hg
  have h3 := (polyGrowth_add n _ _ h1 h2).1
  convert h3 using 1
  funext p
  simp

theorem phpA_pg_y1 (n : ℕ) : PolyGrowth n (fun p : ℝ × (ℝ × ℝ) => p.2.1) :=
  polyGrowth_clm n (ContinuousLinearMap.fst ℝ ℝ ℝ) (fun p => p.2) (polyGrowth_snd n)

theorem phpA_pg_y2 (n : ℕ) : PolyGrowth n (fun p : ℝ × (ℝ × ℝ) => p.2.2) :=
  polyGrowth_clm n (ContinuousLinearMap.snd ℝ ℝ ℝ) (fun p => p.2) (polyGrowth_snd n)

theorem phpA_pos (ν : ℝ) (hν : 0 < ν) (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : 0 < ageA ν s := by
  unfold ageA
  have := mul_pos hν (Set.mem_Ioi.mp hs)
  linarith

theorem phpA_pg_entry (ν : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (A : ℝ → Mat3) (hA : ContDiffOn ℝ 6 A (Ioi 0)) (i j : Fin 3) :
    PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => χ (ν * p.1) * A p.1 i j) := by
  refine polyGrowth_of_s 2 (fun s => χ (ν * s) * A s i j) ?_
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => χ (ν * s)) :=
    hχ.comp (contDiff_const.mul contDiff_id)
  have h1 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s : ℝ => χ (ν * s)) (Ioi 0) :=
    (hc.of_le (by norm_num)).contDiffOn
  have h2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s : ℝ => A s i j) (Ioi 0) :=
    (contDiffOn_pi.1 (contDiffOn_pi.1 hA i) j).of_le
      (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 6))
  exact h1.mul h2

theorem phpA_pg_al (ν : ℝ) (hν : 0 < ν) :
    PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => (ageA ν p.1 ^ 2)⁻¹) := by
  refine polyGrowth_of_s 2 (fun s => (ageA ν s ^ 2)⁻¹) ?_
  have hl : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s : ℝ => ageA ν s) := by
    unfold ageA; fun_prop
  have hl2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s : ℝ => ageA ν s ^ 2) (Ioi 0) :=
    (hl.pow 2).contDiffOn
  exact hl2.inv (fun s hs => pow_ne_zero 2 (phpA_pos ν hν s hs).ne')

theorem phpA_pg_be (ν : ℝ) (hν : 0 < ν) :
    PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => -(2 * ageA ν p.1)⁻¹) := by
  refine polyGrowth_of_s 2 (fun s => -(2 * ageA ν s)⁻¹) ?_
  have hl : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s : ℝ => 2 * ageA ν s) := by
    unfold ageA; fun_prop
  have hl2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s : ℝ => 2 * ageA ν s) (Ioi 0) :=
    hl.contDiffOn
  exact (hl2.inv (fun s hs => (mul_pos two_pos (phpA_pos ν hν s hs)).ne')).neg

theorem phpA_growth_proof (as : ℝ) (χf : ℝ → ℝ) : PhpA_growth as χf := by
  intro hχ ν hν A hA
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χf := hχ.smooth
  have hal := phpA_pg_al ν hν
  have hbe := phpA_pg_be ν hν
  have hy1 := phpA_pg_y1 2
  have hy2 := phpA_pg_y2 2
  have h00 : PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => χf (ν * p.1) * A p.1 0 0) :=
    phpA_pg_entry ν χf hχs A hA.smooth 0 0
  have h02 : PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => χf (ν * p.1) * A p.1 0 2) :=
    phpA_pg_entry ν χf hχs A hA.smooth 0 2
  have h20 : PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => χf (ν * p.1) * A p.1 2 0) :=
    phpA_pg_entry ν χf hχs A hA.smooth 2 0
  have h22 : PolyGrowth 2 (fun p : ℝ × (ℝ × ℝ) => χf (ν * p.1) * A p.1 2 2) :=
    phpA_pg_entry ν χf hχs A hA.smooth 2 2
  have key : PhpA ν χf A = fun p : ℝ × (ℝ × ℝ) =>
      ((ageA ν p.1 ^ 2)⁻¹ *
          ((χf (ν * p.1) * A p.1 0 0) * (-p.2.2) + (χf (ν * p.1) * A p.1 0 2) * p.2.1 -
            ((-(2 * ageA ν p.1)⁻¹) *
                (p.2.1 * ((χf (ν * p.1) * A p.1 0 0) * p.2.1 + (χf (ν * p.1) * A p.1 0 2) * p.2.2) +
                  p.2.2 * ((χf (ν * p.1) * A p.1 2 0) * p.2.1 + (χf (ν * p.1) * A p.1 2 2) * p.2.2))
              * (-p.2.2) +
              -((χf (ν * p.1) * A p.1 2 0) * p.2.1 + (χf (ν * p.1) * A p.1 2 2) * p.2.2))),
       (ageA ν p.1 ^ 2)⁻¹ *
          ((χf (ν * p.1) * A p.1 2 0) * (-p.2.2) + (χf (ν * p.1) * A p.1 2 2) * p.2.1 -
            ((-(2 * ageA ν p.1)⁻¹) *
                (p.2.1 * ((χf (ν * p.1) * A p.1 0 0) * p.2.1 + (χf (ν * p.1) * A p.1 0 2) * p.2.2) +
                  p.2.2 * ((χf (ν * p.1) * A p.1 2 0) * p.2.1 + (χf (ν * p.1) * A p.1 2 2) * p.2.2))
              * p.2.1 +
              ((χf (ν * p.1) * A p.1 0 0) * p.2.1 + (χf (ν * p.1) * A p.1 0 2) * p.2.2)))) := by
    funext p
    refine Prod.ext ?_ ?_
    · simp only [PhpA, merApply, Jrot, Ay, Pi.smul_apply, smul_eq_mul, Prod.smul_fst,
        Prod.fst_sub, Prod.fst_add]
      ring
    · simp only [PhpA, merApply, Jrot, Ay, Pi.smul_apply, smul_eq_mul, Prod.smul_snd,
        Prod.snd_sub, Prod.snd_add]
      ring
  rw [key]
  refine phpA_pg_pair 2 _ _ ?_ ?_ <;>
  repeat' (first
    | exact hal | exact hbe | exact hy1 | exact hy2
    | exact h00 | exact h02 | exact h20 | exact h22
    | apply phpA_pg_mul | apply phpA_pg_add | apply phpA_pg_sub | apply phpA_pg_neg)

end UnforcedLeray.Short.PartIIIb.Concrete
