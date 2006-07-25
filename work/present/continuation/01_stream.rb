require "Stream"

class Unit
	def initialize(name)
		super()
		@name = name
		@env = nil
		@ordered = false
	end

	def step
		if @env
			if @ordered
				print "#@name :: "
			else
				print "#@name, #{@env.msg} :: "
				@ordered = true
			end
			response = gets.chomp
			if response != ""
				@env.respond(response) { @env = nil }
			end
		else
			puts "#@name, no order"
		end
	end

	def order(env)
		@env.respond("Order cancelled") do
			@env = env
			@ordered = false
			@env.ack
		end
	end
end


class TrioAttack
	include Stream

	def initialize(units, dest)
		super()
		raise "Must have exactly 3 units" unless units.length == 3
		@units = units
		@dest = dest
	end
	
	def stream
		parallel_and [
			proc { |e| @units[0].order(e.env("Go to the west of #@dest")) },
			proc { |e| @units[1].order(e.env("Go to the south of #@dest")) },
			proc { |e| @units[2].order(e.env("Go to the east of #@dest")) },
		]

		@units[1].order(env("Engage #@dest from the south, report when there is a strong opposing force"))

		parallel_and [
			proc { |e| @units[0].order(e.env("Engage #@dest from the west" )) },
			proc { |e| @units[2].order(e.env("Engage #@dest from the east" )) },
		]
	end
end


class InfoAttack
	include Stream
	
	def initialize(units, dest)
		super()
		raise "Must have exactly 3 units" unless units.length == 3
		@units = units
		@dest = dest
	end

	def stream
		numunits = @units[0].order(env("How many units does #@dest have?")).to_i
		if numunits < 3
			@units[0].order(env("Conquer #@dest"))
		elsif numunits < 6
			TrioAttack.new(@units, @dest).run
		else
			@units[0].order(env("Return to home base, we cannot conquer such a large force"))
		end
	end
end


units = [ "Alice", "Bob", "Charlie" ].map { |name| Unit.new(name) }
InfoAttack.new(units, "Doomedsburg").run

while true
	units.map { |u| u.step }
end
