type id = Id of int
let id i = Id i
let id2s (Id i) = string_of_int i

type n = N of int
let next (N n ) = N (n+1)
let n2s (N n) = string_of_int n

type 'v kind = 
  | Prepare   
  | Promise of 'v option
  | Accept  of 'v
  | Accepted  

type 'v message = {n:n; s:id; t:id; k:'v kind}

module Ballot = struct 
  type 'v t = { allowed : id list; 
                nones : (id list) * int;
                somes : ('v * (id list) * int) list }

  let make allowed v0 id = {allowed; nones = [],0; somes = [(v0,[id],1)]}

  let quorum b = (List.length b.allowed / 2) + 1

  let register_vote (b:'v t) source (vo:'v option) = 
    if not (List.mem source b.allowed) 
    then b
    else
      match vo with 
        | None -> let (who,c) = b.nones in
                  if List.mem source who 
                  then b
                  else {b with nones = (source::who, c+1) }
        | Some v ->  
          let rec loop acc = function
            | [] -> (v, [source], 1) :: acc
            | (x, who , c) :: rest when x = v -> 
              if not (List.mem source who )
              then (v, source :: who, c+1) :: acc @ rest
              else (v, who, c) :: acc @ rest  
            | x :: rest -> 
              let acc' = x :: acc  in 
              loop acc' rest
          in
          let somes' = loop [] b.somes in
          { b with somes = somes'}
            

  let most_popular (b: 'v t) = 
    let rec find ( (bv, bc) as best) = function
      | [] -> best
      | (v, _, c) :: rest -> 
        let best' = if c > bc then (v,c) else best in
        find best'  rest
    in
    match b.somes with
      | [] -> failwith "empty"
      | (v,_,c) :: rest -> find (v,c) rest
      
  let n_nones (b: 'v t) =
    let (_,c) = b.nones in c

  let have_majority b = 
    let nones = n_nones b in
    let (_,pc) = most_popular b in
    pc + nones >= quorum b

  let pick_value ballot = let (pv, _) =  most_popular ballot in pv

end

let kind2s = function
  | Prepare    -> "Prepare"
  | Promise vo -> "Promise"
  | Accept v   -> "Accept" 
  | Accepted   -> "Accepted"

let msg2s m= Printf.sprintf "(%s,%s,%s,%s)" (n2s m.n) (id2s m.s) (id2s m.t) (kind2s m.k)

type 'v proposal = 'v * 'v Ballot.t

type 'v agent_state = 
  | SHalted 
  | SIdle 
  | SRequest  of ('v proposal)
  | SPromised of 'v option
  | SLead of ('v * int) (* value, outstanding acks *)


type 'v agent = { 
  id : id;
  pop : id list;
  _n : n;
  state : 'v agent_state;
  store : (n * 'v) list;
}

let make_agent id pop = {id; pop; _n = N 0; state = SIdle; store = [];}

let is_idle a = a.state = SIdle
let is_halted a = a.state = SHalted
  

let others agent = List.filter ((<>) agent.id) agent.pop


let start agent value = 
  match agent.state with
    |SIdle ->
      let me = agent.id in
      let n' = next agent._n  in
      let targets = others agent in
      let ballot = Ballot.make targets value me in
      let broadcast = List.map (fun id -> {n= n'; s = me; t = id; k = Prepare}) targets in
      let agent' = {agent with 
        _n = n';
        state = SRequest (value, ballot);
      }
      in
      agent', broadcast
    | _ -> failwith "can't start here"

let halt agent = {agent with state = SHalted}

module type ALGO = sig
  val handle_message : 'v agent -> 'v message -> 'v agent * 'v message list
end

type 'v network = 'v message list
type 'v agents  = 'v agent list
type 'v state   = { net: 'v network; ags: 'v agents}

let find_agent agents sid = List.find (fun a -> a.id = sid) agents    
let replace_agent agent agents = List.map (fun x -> if x.id = agent.id then agent else x) agents

let is_bad state = List.fold_left (fun acc ag -> acc || is_halted ag) false state.ags 

type 'v move = 
  | DeliverMsg of 'v message
  | Wipe of id
      
let move2s = function
  | DeliverMsg msg -> Printf.sprintf "Deliver %s" (msg2s msg)
  | Wipe id        -> Printf.sprintf "Wipe %s" (id2s id)
    
let move2l = function
  | DeliverMsg m -> 
    Printf.sprintf "%s->%s:%s;(n=%s)" 
      (id2s m.s) (id2s m.t) (kind2s m.k) (n2s m.n)
  | Wipe id           -> Printf.sprintf "wipe %s" (id2s id)
    
let generate_moves state = 
  if is_bad state 
  then []
  else
    let deliver = List.map (fun x -> DeliverMsg x) state.net in
    let id3 = Id 3 in
    let agent = find_agent state.ags id3 in
    let wipe = 
      if is_halted agent 
      then [] 
      else [Wipe id3]
    in
    deliver @ wipe 
    
      

let state_label state= 
  let as2l = function
    | SIdle           -> "I"
    | SRequest (_,_)  -> "R"
    | SPromised _     -> "P"
    | SLead (_,_)     -> "L"
    | SHalted         -> "H"
  in
  List.fold_left (fun acc a -> acc ^ (Printf.sprintf "%s%s" (as2l a.state) (n2s a._n))) "" state.ags
    
module type VALUE = sig
  type t
end

module Simulator(A:ALGO)(V:VALUE) = struct
  type v = V.t
  type path = (v move * v state) list

  exception Bad of (path * v state)

  module TSet = Set.Make(struct 
    type t = (string * v move * string)
    let compare = Pervasives.compare
  end)

  let remove x net  = List.filter (fun m -> m <> x) net 

  let execute_move move state path observed = 
    
    let deliver m ag = 
      let agent = find_agent ag m.t in
      let agent', extra = A.handle_message agent m in
      let ag' = replace_agent agent' ag in
      ag', extra
    in
    
    let state' = 
      match move with
        | DeliverMsg m -> 
          let net' = remove m state.net in
          let ags',extra = deliver m state.ags in
          { net = net' @ extra; ags = ags'}
        | Wipe id ->
          let agent = find_agent state.ags id in
          let clean = make_agent id agent.pop in
          let ags' = replace_agent clean state.ags in
          {state with ags = ags'}
    in
    let observed' = 
      let transition = (state_label state, move, state_label state') in
      TSet.add transition observed in
    state' , (move,state) :: path , observed'

  let dump_path path = 
    let rp = List.rev path in
    List.iter 
      (fun (move,state) -> 
        match move with 
          | DeliverMsg m -> Printf.eprintf "%s ---(%s:%8s) ---> %s\n" 
            (id2s m.s) (n2s m.n) (kind2s m.k) (id2s m.t)
          | _ -> Printf.eprintf "%s\n" (move2s move)
      ) rp      
      
  let is_consistent state =
    let rec loop first = function
      | [] -> true
      | agent :: rest ->
        begin
          if agent.state = SIdle then
            match first with
              | None -> loop (Some (agent.id, agent._n, agent.store)) rest
              | Some (id, n,store) ->
                if n = agent._n 
                then store = agent.store && loop first rest
                else loop first rest
          else loop first rest
        end
    in
    loop None state.ags

  let limit = 10
    
  let rec check_all level state path observed = 
    if not (is_consistent state) then raise (Bad (path,state));
    if level = limit
    then observed
    else
      let rec loop observed = function
        | [] -> observed
        | move :: rest ->
          let state', path', observed' = execute_move move state path observed in
          let observed'' = check_all (level + 1) state' path' observed' in
          loop observed'' rest
      in
      let moves = generate_moves state in
      loop observed moves

  let run state0 = check_all 0 state0 [] TSet.empty 

  let dottify state0 observed = 
    Printf.printf "digraph \"basic paxos\" {\n\trankdir=LR\n";
    Printf.printf "\tnode [shape = \"box\"]\n";
    Printf.printf "\t%s\n" (state_label state0);
    TSet.iter (fun (l0,m,l1) -> 
      let ms, extra = match m with
        | Wipe _ -> 
          (move2s m),                       
          "fontcolor=red color=red constraint=false"
        | DeliverMsg m   -> Printf.sprintf"{%s;%s->%s;n=%s}" (kind2s m.k) 
          (id2s m.s) (id2s m.t) (n2s m.n), "" 
      in
      if l0 <> l1 then
        let s = Printf.sprintf "\t%s -> %s [label=\"%s\" %s]\n" l0 l1 ms extra in      
        print_string s) 
      observed;
    Printf.printf "}\n"
end

module StringValue = struct type t = string end
module Mark0 = (struct
  let handle_message agent message = halt agent, []

end : ALGO)

module Mark1 = (struct

  let prepare_when_idle source n agent= 
    let an = agent._n in
    if n > an 
    then
      let pv = None in
      let agent' = {agent with state = SPromised pv; _n = n;} in
      let msg = {n = n;s = agent.id;t = source; k = Promise pv } in
      let out = [msg] in
      agent', out
    else
      halt agent,[]
    
  let promise_for_request (source:id) (mn:n) vo (proposal:'v proposal) agent = 
    let pv,pballot = proposal in
    if mn = agent._n
    then
      let pballot' = Ballot.register_vote pballot source vo in
      if Ballot.have_majority pballot' 
      then
        let value = Ballot.pick_value pballot' in
        let outstanding_acks = Ballot.quorum pballot' -1 in
        let me = agent.id in
        let targets = others agent in
        let make_msg t = {n = mn; s = me; t ; k =  Accept value} in
        let broadcast = List.map make_msg targets in
        let agent' = { agent with 
            store = (mn,value) :: agent.store;
            state = SLead (value, outstanding_acks);
        }
        in
        agent', broadcast
      else
        agent, []
    else
      halt agent, []
        
  let handle_accept m v agent = 
    match agent.state with
      | SPromised vo when agent._n = m.n -> 
        let agent' = {agent with state = SIdle; store = (m.n, v) :: agent.store;} in
        let out = [{n = m.n;s = agent.id;t = m.s;k = Accepted}] in
        agent', out
      | _ -> halt agent, []
    
      
  let handle_accepted m agent =
    match agent.state with
      | SLead (v,out) when agent._n = m.n -> 
        let out' = out -1 in
        let state' = if out' = 0 then SIdle else SLead(v,out') in
        {agent with state = state'},[]          
      | _ -> halt agent, []


  let handle_message agent m = 
    match m.k with
      | Prepare when agent.state = SIdle -> prepare_when_idle m.s m.n agent
      | Promise vo -> 
        begin
          match agent.state with 
            | SRequest p -> promise_for_request m.s m.n vo p agent
            | _ -> halt agent, []
        end
      | Accept v -> handle_accept m v agent
      | Accepted -> handle_accepted m agent
      | _ -> halt agent,[]
end : ALGO)

module Mark2 = (struct

  let prepare_when_idle source n agent= 
    let an = agent._n in
    if n > an 
    then
      let pv = None in
      let agent' = {agent with state = SPromised pv; _n = n;} in
      let msg = {n = n;s = agent.id;t = source; k = Promise pv } in
      let out = [msg] in
      agent', out
    else
      halt agent,[]
    
  let promise_for_request (source:id) (mn:n) vo (proposal:'v proposal) agent = 
    let pv,pballot = proposal in
    if mn = agent._n
    then
      let pballot' = Ballot.register_vote pballot source vo in
      if Ballot.have_majority pballot' 
      then
        let value = Ballot.pick_value pballot' in
        let outstanding_acks = Ballot.quorum pballot' -1 in
        let me = agent.id in
        let targets = others agent in
        let make_msg t = {n = mn; s = me; t ; k =  Accept value} in
        let broadcast = List.map make_msg targets in
        let agent' = { agent with 
            store = (mn,value) :: agent.store;
            state = SLead (value, outstanding_acks);
        }
        in
        agent', broadcast
      else
        agent, []
    else
      halt agent, []
        
  let handle_accept m v agent = 
    let _accept m =         
      let agent' = {agent with _n = m.n; state = SIdle; store = (m.n, v) :: agent.store;} in
      let out = [{n = m.n;s = agent.id;t = m.s;k = Accepted}] in
      agent', out
    in
    match agent.state with
      | SPromised vo when agent._n = m.n -> _accept m
      | SIdle when (next agent._n) = m.n -> _accept m
      | _ -> halt agent, []
    
      
  let handle_accepted m agent =
    match agent.state with
      | SLead (v,out) when agent._n = m.n -> 
        let out' = out -1 in
        let state' = if out' = 0 then SIdle else SLead(v,out') in
        {agent with state = state'},[]          
      | SIdle when agent._n = m.n -> agent,[]
      | _ -> halt agent, []


  let handle_message agent m = 
    match m.k with
      | Prepare when agent.state = SIdle -> prepare_when_idle m.s m.n agent
      | Promise vo -> 
        begin
          match agent.state with 
            | SRequest p -> promise_for_request m.s m.n vo p agent
            | SLead(v,out) when agent._n = m.n -> agent, []
            | SIdle when agent._n = m.n -> agent, []
            | _ -> halt agent, []
        end
      | Accept v -> handle_accept m v agent
      | Accepted -> handle_accepted m agent
      | _ -> halt agent,[]
end : ALGO)

module Mark3 = (struct

  let handle_prepare m agent = 
    match agent.state with 
      |SIdle ->
        begin
          let an = agent._n in
          if m.n = next an 
          then
            let pv = None in
            let agent' = {agent with state = SPromised pv; _n = m.n;} in
            let msg = {n = m.n;s = agent.id;t = m.s; k = Promise pv } in
            let out = [msg] in
            agent', out
          else
            if m.n <= an 
            then agent,[]
            else halt agent,[]
        end
      | _ -> halt agent, []
    
  let promise_for_request (source:id) (mn:n) vo (proposal:'v proposal) agent = 
    let pv,pballot = proposal in
    if mn = agent._n
    then
      let pballot' = Ballot.register_vote pballot source vo in
      if Ballot.have_majority pballot' 
      then
        let value = Ballot.pick_value pballot' in
        let outstanding_acks = Ballot.quorum pballot' -1 in
        let me = agent.id in
        let targets = others agent in
        let make_msg t = {n = mn; s = me; t ; k =  Accept value} in
        let broadcast = List.map make_msg targets in
        let agent' = { agent with 
            store = (mn,value) :: agent.store;
            state = SLead (value, outstanding_acks);
        }
        in
        agent', broadcast
      else
        agent, []
    else
      halt agent, []
        
  let handle_accept m v agent = 
    let _accept m =         
      let agent' = {agent with _n = m.n; state = SIdle; store = (m.n, v) :: agent.store;} in
      let out = [{n = m.n;s = agent.id;t = m.s;k = Accepted}] in
      agent', out
    in
    match agent.state with
      | SPromised vo when agent._n = m.n -> _accept m
      | SIdle when (next agent._n) = m.n -> _accept m
      | _ -> halt agent, []
    
      
  let handle_accepted m agent =
    match agent.state with
      | SLead (v,out) when agent._n = m.n -> 
        let out' = out -1 in
        let state' = if out' = 0 then SIdle else SLead(v,out') in
        {agent with state = state'},[]          
      | SIdle when agent._n = m.n -> agent,[]
      | _ -> halt agent, []


  let handle_message agent m = 
    match m.k with
      | Prepare -> handle_prepare m agent
      | Promise vo -> 
        begin
          match agent.state with 
            | SRequest p -> promise_for_request m.s m.n vo p agent
            | SLead(v,out) when agent._n = m.n -> agent, []
            | SIdle when agent._n = m.n -> agent, []
            | _ -> halt agent, []
        end
      | Accept v -> handle_accept m v agent
      | Accepted -> handle_accepted m agent
end : ALGO)

module M = Simulator(Mark3)(StringValue)

let main () = 
  let ids = List.map id [1;2;3] in
  let a1,a1_out = start (make_agent (Id 1) ids) "x" in
  let a2,a2_out = (make_agent (Id 2) ids),[] in
  let a3,a3_out = (make_agent (Id 3) ids),[] in
  let world = [a1;a2;a3] in
  let state0 = {net = a1_out @ a2_out @ a3_out; ags = world} in
  try
    let observed = M.run state0 in
    M.dottify state0 observed 
  with (M.Bad (path, state)) ->
    Printf.eprintf "bad path:\n";
    M.dump_path path;
    Printf.eprintf "%s\n" (state_label state)


let () = main ();;



