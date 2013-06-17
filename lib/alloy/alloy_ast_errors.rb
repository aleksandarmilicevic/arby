module Alloy
  module Ast

    #-----------------------------------------------------
    # == Class +TypeError+
    #
    # Raised in case of various type errors (e.g., trying
    # to extend a sig from the +String+ class).
    #-----------------------------------------------------
    class TypeError < StandardError
    end

    class ResolveError < StandardError
    end

  end
end
