struct

    module Fctr = functor(X : sig val diff : int end) 
    struct
        val fcall = false
    end

end

