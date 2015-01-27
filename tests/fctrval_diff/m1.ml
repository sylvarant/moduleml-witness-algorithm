struct

    module Inner =
    struct
        val diff = 5
    end

    module Fctr = functor(X : sig val diff : int end) 
    struct
        val fcall = false
    end

end

