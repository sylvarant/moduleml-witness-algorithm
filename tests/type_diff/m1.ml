struct

    (* has abstract type t *)
    module Abstract : (sig 
        type t; 
        val func : t -> t; 
        val create : t; 
    end) =
    struct
        type t = int
        val create = 5
        val func x = x * 2
    end

end

