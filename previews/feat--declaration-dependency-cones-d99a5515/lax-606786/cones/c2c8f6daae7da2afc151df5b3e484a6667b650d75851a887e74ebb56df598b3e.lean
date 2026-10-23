-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

-- Lax606786.MeasurableSelection
section
namespace Lax606786.MeasurableSelection

/-- A map into a separable metric space is measurable when its distance to every point is. -/
axiom measurable_of_measurable_dist {Y Ω : Type*} [MetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω] {F : Ω → Y}
    (h : ∀ y : Y, Measurable fun ω => dist (F ω) y) : Measurable F

end Lax606786.MeasurableSelection
end
