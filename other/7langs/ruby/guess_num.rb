#!/usr/bin/env ruby

def main
  n = rand(10)
  puts "I've guessed number from 0 to 9. What is it?"
  loop do
    print "Enter your guess: "
    begin
      s = gets.chomp
      guess = Integer(s)
    rescue ArgumentError
      puts "Wrong number '#{s}'."
      next
    rescue Interrupt
      puts "\nBye!"
      return
    end
    if guess == n
      puts "You are right!"
      return
    elsif guess < n
      puts "Your guess is lower then the number."
    else
      puts "Your guess is greater then the number."
    end
  end
end

if __FILE__ == $0
  main
end
