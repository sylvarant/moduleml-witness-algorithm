struct

    (* has abstract type y *)
    module Abstract : (sig 
        type y; 
        val func : y -> y; 
        val create : y; 
    end) =
    struct
        type y = int
        val create = 5
        val func x = x * 2
    end

end

