(* This file has been generated automatically by some OCaml scripts. *)
(* Please do not edit it, or your changes will probably be erased later. *)

(******************************************)

Require Import JsCommon.
Require Import JsCommonAux.
Require Import JsPrettyInterm.
Require Import JsPrettyIntermAux.
Require Import JsSyntaxInfos.
Require Import JsInit.

(******************************************)


(******************************************)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type lp : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type vi : value.
Implicit Type vp : value.
Implicit Type vthis : value.
Implicit Type r : ref.
Implicit Type ty : type.
Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.
Implicit Type ct : codetype.
Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.
Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.
Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.
Implicit Type c : call.
Implicit Type cstr : construct.
Implicit Type xs : (list prop_name).
Implicit Type sb : switchbody.
Implicit Type sc : switchclause.

(******************************************)

Inductive js_names :=
