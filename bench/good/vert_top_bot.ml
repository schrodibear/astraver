
(* pvs "IMPORTING Const, vector3, reals@sq, reals@sqrt" *)

pvs "vector3: TYPE
  x,y,z : [vector3 -> real]
  sqrt: [real -> real]
  listv: TYPE
  cons: [real,real,real,listv -> listv]
  pre_vtb: bool
  correct: [listv -> bool]
  D,H: real
  pre_visible: [vector3,real,real -> bool]
  post_visible: [vector3,real,real,bool -> bool]
"

external x,y,z : (v:vector3) float

external A,B,C,Delta,t1,t2,x1,x2,nvoz1,nvoz2 : float ref

external D : float
external H : float
external eps : float

external visible : 
  (a:vector3)(x:float)(eps:float)
  returns result:bool pre  pre_visible(a,x,eps)
                      post post_visible(a,x,eps,result) end

external res : listv ref
external cons : (ex:float)(ey:float)(ez:float)(l:listv) listv


let vert_top_bot =
  fun (a:vector3)(vo:vector3)(vi:vector3)(eps:float) ->
  { pre_vtb }
 (if (x vo) /= (x vi) || (y vo) /= (y vi) then 
  begin
    A := ((x vo) - (x vi)) * ((x vo) - (x vi)) 
       + ((y vo) - (y vi)) * ((y vo) - (y vi));
    B := 2.0 * (x a) * ((x vo) - (x vi));
    C := (x a) * (x a) - D * D;
    Delta := !B * !B - 4.0 * !A * !C;
    if !Delta >= 0.0 then begin
      t1 := (- !B - (sqrt !Delta)) / (2.0 * !A);
      t2 := (- !B + (sqrt !Delta)) / (2.0 * !A);
      x1 := (x a) + !t1 * ((x vo) - (x vi));
      x2 := (x a) + !t2 * ((x vo) - (x vi));
     (if !t1 > 0.0 && (visible a !x1 eps) then begin
	nvoz1 := (eps * H - (z a)) / !t1 + (z vi);
	res := (cons (x vo) (y vo) !nvoz1 !res)
      end)
      { correct(res) };
      if !t2 > 0.0 && (visible a !x2 eps) then begin
	nvoz2 := (eps * H - (z a)) / !t2 + (z vi);
	res := (cons (x vo) (y vo) !nvoz2 !res)
      end
    end 
  end else 
    res := (cons (x vo) (y vo) (z vi) !res))
  { correct(res) }

