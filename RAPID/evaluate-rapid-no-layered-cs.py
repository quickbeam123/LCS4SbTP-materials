import vampire_lib
import rapid_lib
import os

vampire_exec = "/home/sudamar2/rapid/run_vampire.sh"
input_dir = "/home/sudamar2/rapid/arrays-user-conjectures"

timeout = 60

user_options_list = rapid_lib.getPortfolioConfigurationsRapidNoLayeredCS(timeout)

rapid_lib.printPortfolioStats(user_options_list, timeout, len(os.listdir(input_dir)))

vampire_lib.run_vampire_portfolio_on_dir(vampire_exec, input_dir, user_options_list, True, "")
