import VReact.Attr
/-!
# List facts for automation

React state is mostly immutable lists updated by `filter` (remove), `map`
(update) and append (insert); keyed lists require distinct keys.  These lemmas
let `grind` move key-uniqueness and membership facts through those operations.
-/
namespace VReact

/-- Removing elements keeps keys distinct. -/
theorem nodup_map_filter {α β} (f : α → β) (p : α → Bool) (l : List α) (h : (l.map f).Nodup) :
    ((l.filter p).map f).Nodup :=
  h.sublist ((List.filter_sublist).map f)
grind_pattern nodup_map_filter => (l.filter p).map f, (l.map f).Nodup

attribute [grind →] List.mem_of_find?_eq_some
attribute [grind =] List.all_eq_true List.any_eq_true

-- membership and distinctness distribute over the list operations
attribute [vreact_simp] List.nodup_append List.map_append List.mem_append List.mem_map List.mem_filter
  List.nodup_cons List.mem_singleton List.nodup_nil List.filter_append List.append_assoc

end VReact
