class Stream
	def run(cont, ans)
		@return = cont
		if @continue
			@continue.call(ans)
		else
			stream(ans)
		end
	end
	
	def ask(q)
		callcc do |cont|
			@continue = cont
			@return.call(q)
		end
	end
end


class ProddyStream < Stream
	def stream(ans)
		yn = "no"
		while yn != "yes"
			name = ask("What is your name?")
			yn = ask("Your name is " + name + ", correct?");
		end
	end
end


stream = ProddyStream.new
ans = ""
while true
	quest = callcc do |cont|
		stream.run(cont, ans)
	end
	print quest + " "
	ans = gets.chomp
end
