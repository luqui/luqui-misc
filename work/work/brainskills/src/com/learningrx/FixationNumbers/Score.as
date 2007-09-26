package com.learningrx.FixationNumbers
{
	public class Score
	{
		private var _PassingPercent:Number = 90;
		private var _ExcellingPercent:Number = 95;
		private var _Parent:Game;

		public function Score(pParent:Game)
		{
			_Parent = pParent;
		}

		public function CheckPercentCorrect(pNumCorrect:Number):void
		{
			var medal90:Number = (speed + 1) * 10;
			var percentCorrect:Number = Math.floor(100 * (pNumCorrect / medal90));
			if (pPercentCorrect >= _PassingPercent)
			{
				SetEndText1("Congratulations - going on to the next level!");
				UpdateSetupScreen(current_level, sublevel, 2)
				if (sublevel == 4)
				{
					current_level += 1;
					sublevel = 1;	
				}
				else if (sublevel < 4)
				{
					sublevel += 1;
				}
				if (pPercentCorrect >= _ExcellingPercent)
				{
					if (speed < 4)
					{
						SetSpeed(GetSpeed() + 1);
						SetEndText2("(Speed increasing!)");
					}
				}
			}
			else
			{
				UpdateSetupScreen(current_level, sublevel, 1)
				SetEndText1("Keep practicing!");
				if(speed > 1)
				{
					SetSpeed(GetSpeed() - 1);
					SetEndText2("(Speed decreasing)");
				}
			}
		}
	}
}