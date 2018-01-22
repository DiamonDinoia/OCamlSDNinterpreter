
(* type created in order to expand the implementation with structured data if needed *)
type data = Data ;;

(* result of the routing function *)
type interface = Nothing | Port of int ;;

(* action to perform on the pachets, used in rules *)
type action = Drop | Route ;;

(* internal status of the routers *)
type status = Blocking | Routing | Uninitialized ;;

(* type of the identifier in order to implement an enviroment  *)
type ide = string ;;

(* type of result of the evaluation of the interpreter *)
type eval =
    | Router of router
    | Rule of rule
    | Table of table
    | Packet of packet
    | Interface of interface
    | Action of action
    | Policy of policy
    | Int of int
    | Status of status
    | Data of data
(* structured type representig a rule *)
and rule = { routing_address: eval; action: eval; interface: eval }
(* the table is a rule list the type are checked at run-time *)
and table = eval list
and router = { routing_table: eval; status: eval; policy: eval }
and packet = { source_address: eval; dest_address: eval; data: eval }
(* the security policy is a generic function from packet to boolean *)
and policy = packet -> bool ;;

(* type that models the sintax of the language *)
type exp =
(* Let and Den are not required implement only in order to have an enviroment *)
    | Let of ide * exp * exp
    | Den of ide
    | EInt of int
    | EInterface of interface
    | EAction of action
    | EPolicy of policy
    | ERule of rule
    | EData of data
    | ERouter of router
    (* install a table into a router  *)
    | Install of exp * exp
    (* block traffic through a router *)
    | Block of exp
    (* unlock traffic through  a router *)
    | Unlock of exp
    (* apply a policy to a router *)
    | Apply_policy of exp * exp
    (* create a new routing rule *)
    | Create_rule of exp * exp * exp
    (* creating a routing table from a rule list *)
    | Create_table of exp list
    (* set a rule to drop *)
    | Drop_rule of exp * exp
    (* set a rule to route through a different interface (mobility) *)
    | Move_rule of exp * exp ;;

(* auxiliary functons used in simulation *)
let create_router () = ERouter {routing_table=Table []; status = Status Uninitialized; policy=Policy (fun _ -> true)}

let create_packet source dest = {source_address=source; dest_address=dest; data=Data Data}

(* routing function implements the behaviour of the router *)
let route (router:router) (packet: packet) = match (router.routing_table,router.status,router.policy,packet.dest_address) with
    (* check if the parameters are correct  *)
    | (Table table,Status status,Policy policy, Int address) -> (
            (* check if the router is enabled and apply the security policy *)
            if status=Routing && policy(packet) then (
                (* auxiliary inner function to find the correct rule *)
                let rec match_rule (table:table) = match table with
                    | [] -> Interface Nothing
                    | x::xs -> ( match x with
                                | Rule x -> if x.routing_address = packet.dest_address then x.interface else match_rule xs
                                | _ -> failwith "type error" )
            in match router.routing_table with
                | Table t -> match_rule t
                | _ -> failwith "type error" )
            (* if there is no rule for the packet fails *)
            else Interface Nothing )
    | _ -> failwith "type error"

(* enviroment *)
type 't env = (string * 't) list ;;

(* lookup in enviroment *)
let rec lookup x y = match x with
                         | (i1,e1) :: x1 -> if y = i1 then e1 else lookup x1 y
                         | [] -> failwith("undeclared ide") ;;

(* add an identifier into the enviroment *)
let bind ((r :eval env), (i :ide), (e  :eval)) =  (i,e) :: r ;;

(* drop_rule, simply find the rule make the change and return the new table (immutabilty) *)
let drop_rule rule table =
    let rec f l = match l with
        | [] -> []
        | x::xs -> ( match x with
            | Rule r -> if r.routing_address=rule.routing_address then
                            Rule {routing_address=r.routing_address; action=Action Drop; interface=r.interface}::f xs
                        else Rule r::f xs
            | _ -> failwith "type error" )
    in f table ;;

(* drop_rule, simply find the rule change the intrface and return the new table (immutabilty) *)
let move_rule rule table =
    let rec f l = match l with
        | [] -> []
        | x::xs -> ( match x with
            | Rule r -> if r.routing_address=rule.routing_address then
                            Rule {routing_address=r.routing_address; action=r.action; interface=rule.interface}::f xs
                        else Rule r::f xs
            | _ -> failwith "type error" )
    in f table ;;

(* install a new table into a router, with type checking *)
let install (table:eval) (router: eval) = match table,router with
    | (Table t, Router r) -> Router { routing_table=table; status=r.status; policy=r.policy }
    | _ -> failwith "type error" ;;

(* definition of the semantic of the language *)
let rec sem ((e:exp), (r: eval env)) = match e with
    | Den n -> lookup r n
    | Let(i, e1, e2) -> sem(e2, bind (r, i, sem(e1, r)))
    | EInterface i -> Interface i
    | EPolicy p -> Policy p
    | EAction a -> Action a
    | ERule r -> Rule r
    | EData d -> Data d
    | EInt i -> Int i
    | ERouter r -> Router r
    | Install (table, router) ->  install (sem(table,r)) (sem(router,r))
    | Block (router) ->  ( match sem(router,r) with
            | Router r  ->  Router { routing_table=r.routing_table; status=Status Blocking; policy=r.policy }
            | _ -> failwith "type error" )
    | Unlock (router) ->  ( match sem(router,r) with
            | Router r  ->  Router { routing_table=r.routing_table; status=Status Routing; policy=r.policy }
            | _ -> failwith "type error" )
    | Apply_policy (policy, router) -> ( match sem(policy,r),sem(router,r) with
            | Policy p, Router r ->  Router { routing_table=r.routing_table; status=r.status; policy=Policy p}
            | _ -> failwith "type error" )
    | Create_rule (address,action,interface) ->
            Rule { routing_address=sem(address,r); action=sem (action,r); interface=sem (interface,r) }
    | Create_table t -> Table (List.map (fun x -> sem(x,r)) t)
    | Drop_rule(rule,table) -> (    match sem(rule,r),sem(table,r) with
        | (Rule rule, Table table) -> Table ( drop_rule rule table )
            | _ -> failwith "unbuond error" )
    | Move_rule(rule,table) -> (    match sem(rule,r),sem(table,r) with
        | (Rule rule, Table table) -> Table ( move_rule rule table )
            | _ -> failwith "unbuond error" )   ;;

(* simulation *)

print_string "Begin simulation:\n" ;;

let router01 = create_router ();;
let router02 = create_router ();;
let router03 = create_router ();;

print_string "Detected 3 routers: router01, router02, router03:\n" ;;

let rule01 = Create_rule (EInt (1),EAction Route,EInterface (Port 1)) ;;
let rule02 = Create_rule (EInt (2),EAction Route,EInterface (Port 2)) ;;
let rule03 = Create_rule (EInt (3),EAction Route,EInterface (Port 3)) ;;
let rule04 = Create_rule (EInt (4),EAction Route,EInterface (Port 4)) ;;
let rule05 = Create_rule (EInt (5),EAction Route,EInterface (Port 5)) ;;
let rule06 = Create_rule (EInt (6),EAction Route,EInterface (Port 6)) ;;
let rule07 = Create_rule (EInt (7),EAction Route,EInterface (Port 7)) ;;
let rule08 = Create_rule (EInt (8),EAction Route,EInterface (Port 8)) ;;
let rule09 = Create_rule (EInt (9),EAction Route,EInterface (Port 9)) ;;

print_string "Defined some rules\n" ;;

let table01 = Create_table [ rule01; rule02; rule03 ] ;;
let table02 = Create_table [ rule04; rule05; rule06 ] ;;
let table03 = Create_table [ rule07; rule08; rule09 ] ;;

print_string "Defined some tables\n" ;;

let install01 = Install(table01,router01) ;;
let install02 = Install(table02,router02) ;;
let install03 = Install(table03,router03) ;;

print_string "Installed some rules\n" ;;

let packet01 = create_packet (Int 4) (Int 1) ;;
let packet02 = create_packet (Int 9) (Int 2) ;;
let packet03 = create_packet (Int 4) (Int 4) ;;
let packet04 = create_packet (Int 53) (Int 5) ;;
let packet05 = create_packet (Int 77) (Int 7) ;;
let packet06 = create_packet (Int 765) (Int 9) ;;

print_string "Created some packet\n" ;;

let _ = match sem (install01,[]) with
    | Router r -> route r packet01
    | _ -> failwith "type error, not a router \n" ;;

print_string "router not correctly initialized, routing failed\n" ;;

let init01 = Unlock(install01) ;;
let init02 = Unlock(install02) ;;
let init03 = Unlock(install03) ;;

print_string "routers initialized\n" ;;

let _ = match sem (init01,[]) with
    | Router r -> route r packet01
    | _ -> failwith "type error, not a router \n" ;;

let _ = match sem (init02,[]) with
    | Router r -> route r packet03
    | _ -> failwith "type error, not a router \n" ;;

let _ = match sem (init03,[]) with
    | Router r -> route r packet05
    | _ -> failwith "type error, not a router \n" ;;

print_string "packets correctly routed\n" ;;

let init03 = Block(install03) ;;

let _ = match sem (init01,[]) with
    | Router r -> route r packet01
    | _ -> failwith "type error, not a router \n" ;;

let _ = match sem (init02,[]) with
    | Router r -> route r packet03
    | _ -> failwith "type error, not a router \n" ;;

let _ = match sem (init03,[]) with
    | Router r -> route r packet05
    | _ -> failwith "type error, not a router \n" ;;

print_string "traffic blocked on router03\n" ;;

let drop01 = Drop_rule(rule01,table01) ;;

print_string "rule correctly dropped\n" ;;

let install01 = Install(drop01,router01) ;;

let _ = match sem (install01,[]) with
    | Router r -> route r packet01
    | _ -> failwith "type error, not a router \n" ;;

print_string "packet correctly dropped\n" ;;

let rule01 = Create_rule (EInt (2),EAction Route,EInterface (Port 1)) ;;
let move01 = Move_rule(rule01,table01) ;;
let install01 = Install(move01,router01) ;;
let enable = Unlock(install01) ;;

let _ = match sem (enable,[]) with
    | Router r -> route r packet02
    | _ -> failwith "type error, not a router \n" ;;

print_string "mobility handled correctly\n" ;;
