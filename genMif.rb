puts <<"EOF"
WIDTH = 17;
DEPTH = 1024;
ADDRESS_RADIX = BIN;
DATA_RADIX = BIN;
CONTENT
BEGIN

EOF

ramMap = open("./ramMap.txt", "r")
while line = ramMap.gets
  nums = line.strip.split(",")
  puts "#{nums[0]} : #{nums[1]};"
end

puts "END;"


