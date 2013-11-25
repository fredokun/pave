(** Contains global definitiions that can be used by multiple modules. Avoid
    circular dependencies *)


let global_definition_map : (string, Syntax.definition) Hashtbl.t = Hashtbl.create 64
