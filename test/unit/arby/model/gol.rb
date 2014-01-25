require 'my_test_helper'
require 'curses'

class Cell
  attr_reader :x, :y, :state

  def initialize(x, y, state=:on)
    @x, @y, @state = x, y, state
  end

  def live?() ![:off, :dead, nil].member?(@state) end

  def eql?(other)
    return false unless other
    return false unless other.class == self.class
    self.x == other.x && self.y == other.y
  end

  def hash() [@x, @y, @state].hash end
end

class DeadCell < Cell
  def initialize(x, y) super(x, y, :off) end
  def live?()          false end
  def alive(state=:on) Cell.new(@x, @y, state) end
end

class World
  attr_reader :live_cells

  def initialize(*cells)
    @live_cells = cells
    @grid = {}
    update_grid cells
  end

  def dead_cells(offsets=@@moore_nbr_offs)
    @dead_cells ||= 
      begin
        ans = @live_cells.reduce(Set.new){ |acc, c|
          self.class.nbr(c.x, c.y, offsets).each do |x, y|
            acc << DeadCell.new(x, y)
          end
          acc
        }.to_a
        update_grid ans
        ans
      end
  end 

  def all_cells() live_cells + dead_cells end
  def at(x, y)    col=@grid[x] and col[y] end

  def tick
    new_cells = Set.new
    all_cells.each do |c|
      c_next = tick_cell(c)
      new_cells << c_next if c_next && c_next.live?
    end
    self.class.new *new_cells.to_a
  end

  def moore_nbr(cell)
    self.class.moore_nbr(cell.x, cell.y).map{|x, y| at(x, y)}.compact
  end

  private

  def update_grid(cells, owr=false) cells.each{|c| grid_add(c, owr)} end
  def grid_add(cell, owr=false)
    if owr
      (@grid[cell.x] ||= {})[cell.y] = cell 
    else
      (@grid[cell.x] ||= {})[cell.y] ||= cell 
    end
  end

  @@moore_nbr_offs = [[-1, -1], [0, -1], [1, -1],
                      [-1,  0],          [1,  0],
                      [-1,  1], [0,  1], [1,  1]]

  @@von_neumann_nbr_offs = [          [0, -1]         ,
                            [-1,  0],          [1,  0],
                                      [0,  1]         ]

  def self.moore_nbr(x, y)       nbr(x, y, @@moore_nbr_offs) end
  def self.von_neumann_nbr(x, y) nbr(x, y, @@von_neumann_nbr_offs) end
  def self.nbr(x, y, offsets)    offsets.map{|xx, yy| [x + xx, y + yy]} end
end

class GameOfLife < World
  def tick_cell(cell)
    mn = moore_nbr(cell)
    ln = mn.select(&:live?)
    if cell.live?
      (ln.size < 2 || ln.size > 3) ? nil : cell
    else
      ln.size == 3 ? cell.alive : nil
    end
  end
end

def norm(coords, x_off=0, y_off=0)
  min_x = coords.map{|x, y| x}.min
  min_y = coords.map{|x, y| y}.min
  coords.map{|x, y| Cell.new x - min_x + x_off, y - min_y + y_off}
end

def blinker
  [[1, 0], [1, 1], [1, 2]].map{|x, y| Cell.new(x, y)}
end
def pentomino
  [        [3, 2], [4, 2], 
   [2, 3], [3, 3], 
           [3, 4]        ].map{|x, y| Cell.new(x, y)}
end
def glider
  [        [3, 2], 
                   [4, 3], 
   [2, 4], [3, 4], [4, 4] ].map{|x, y| Cell.new(x, y)}
end

@@gun = [[6, -4], [4, -3], [6, -3], [-6, -2], [-5, -2], [2, -2], [3, -2], [16, -2],
         [17, -2], [-7, -1], [-3, -1], [2, -1], [3, -1], [16, -1], [17, -1], [-18, 0],
         [-17, 0], [-8, 0], [-2, 0], [2, 0], [3, 0], [-18, 1], [-17, 1], [-8, 1], [-4, 1],
         [-2, 1], [-1, 1], [4, 1], [6, 1], [-8, 2], [-2, 2], [6, 2], [-7, 3], [-3, 3],
         [-6, 4], [-5, 4]]

@@bigun = [[-14, -7], [-15, -6], [-14, -6], [-16, -5], [-15, -5], [-15, -4], [-14, -4],
           [-11, -4], [-10, -4], [13, -3], [13, -2], [14, -2], [23, -2], [24, -2], [14, -1],
           [15, -1], [23, -1], [24, -1], [-15, 0], [-14, 0], [-11, 0], [-10, 0], [9, 0],
           [10, 0], [13, 0], [14, 0], [-25, 1], [-24, 1], [-16, 1], [-15, 1], [-25, 2], 
           [-24, 2], [-15, 2], [-14, 2], [-14, 3], [9, 4], [10, 4], [13, 4], [14, 4],
           [14, 5], [15, 5], [13, 6], [14, 6], [13, 7]]

def gun() norm(@@gun, 10, 10) end  
def bigun() norm(@@bigun, 10, 10) end  


def print(win, w)
  win.clear
  w.live_cells.each do |c|
    win.setpos(c.y, c.x)
    win.addch "*"
  end
  win.refresh
end


win = Curses.init_screen

# disable line buffering and handle Ctrl+Z and Ctrl+C manually - don't generate
# signals when these are pressed
# Curses.raw

# disable echoing of inputted characters
Curses.noecho
Curses.curs_set(0)

win.move(10, 10)

w = GameOfLife.new *gun
print(win, w)
i = 0
while i < 400
  sleep(0.1)
  i += 1
  w = w.tick
  print(win, w)
end



# draw on the screen
Curses.refresh

win.addstr "Type any character to finish"

# wait for a key press
Curses.getch
