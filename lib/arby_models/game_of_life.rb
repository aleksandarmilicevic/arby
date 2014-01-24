require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl

  alloy_model :GameOfLife do
    sig Cell [
      x, y: Int
    ]
    # {
    #   no(c2: Cell - self){
    #     x == c2.x && y == c2.y
    #   }
    # }

    sig World [
      cells: (set Cell)
    ]

    fun neighbours[i, j: Int, w: World][set Cell] {
      w.cells.select{ |c|
        (c.x != i || c.y != j) and
        (c.x - j).in?(-1..1) and
        (c.y - j).in?(-1..1)
      }
    }

    pred tick[w, w_next: World] {
      all(c: w.cells) | let(nbrs: neighbours(c.x, c.y, w)) {
        if nbrs.size < 2 || nbrs.size > 3
          !c.in?(w_next.cells)
        else
          c.in?(w_next.cells)
        end
      } and
      all(i, j: Int) {
        if no(c: w.cells){c.x == i && c.y == j} && neighbours(i, j, w).size == 3
          some(c: w_next.cells){c.x == i && c.y == j}
        end
      }
    }
  end


  # alloy_model :GameOfLife do
  #   one sig Cell

  #   sig World [
  #     grid: Int ** Int ** (lone Cell)
  #   ]

  #   fun live_neighbours[x, y: Int, w: World][Int ** Int] {
  #     (Int ** Int).select{|xx, yy|
  #       (xx != x || yy != y) and
  #       (xx - x).in?(-1..1) and
  #       (yy - y).in?(-1..1) and
  #       some w.grid[xx][yy]
  #     }
  #   }

  #   pred tick[w, w_next: World] {
  #     all(x, y: Int) |
  #       let(ln: live_neighbours(x, y, w)) {
  #         if some w.grid[x][y]
  #           if ln.size < 2 || ln.size > 3
  #             some w_next.grid[x][y]
  #           else
  #             no w_next.grid[x][y]
  #           end
  #         else
  #           if ln.size == 3
  #             some w_next.grid[x][y]
  #           else
  #             no w_next.grid[x][y]
  #           end
  #         end
  #       }
  #   }
  # end

end


  # alloy_model :GameOfLife do
  #   one sig Cell [
  #     x, y: Int
  #   ] {
  #     no(c2: Cell - self){
  #       x == c2.x && y == c2.y
  #     }
  #   }

  #   sig World [
  #     cells: (set Cell)
  #   ]

  #   fun neighbours[x, y: Int, w: World][set Cell] {
  #     w.cells.select{ |c|
  #       (c.x != x || c.y != y) and
  #       (c.x - x).in?(-1..1) and
  #       (c.y - y).in?(-1..1)
  #     }
  #   }

  #   pred tick[w, w_next: World] {
  #     all(c: w.cells) | let(nbrs: neighbours(c.x, c.y, w)) {
  #       if nbrs.size < 2 || nbrs.size > 3
  #         !c.in?(w_next.cells)
  #       else
  #         c.in?(w_next.cells)
  #       end
  #     } and
  #     all(x, y: Int) {
  #       if no(c: w.cells){c.x == x && c.y == y} && neighbours(x, y, w).size == 3
  #         some(c: w_next.cells){c.x == x && c.y == y}
  #       end
  #     }
  #   }
  # end
