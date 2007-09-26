package com.learningrx.AttentionArrows
{
	import flash.display.Sprite;
	
	import com.learningrx.*;
	
	public class Distractions extends Sprite
	{
		private var _Parent:Game;
		private var _Alpha:Number;
		
		public function Distractions(pParent:Game)
		{
			_Parent = pParent;
		}

		public function Reset(pDetails:Object):void
		{
			_Alpha = pDetails.Alpha;
			Utilities.RemoveAllChildrenFromDisplayList(this);
			InitMovingArrows(pDetails.MovingArrows);
			//InitSpinningArrows(pDetails.SpinningArrows);
		}
		
		private var _VoiceDirections:Array = [new LeftVoice(),
														  new RightVoice(),
														  new UpVoice(),
														  new DownVoice()];
		
		public function PlayRandomAudioDistraction():void
		{
			if (Utilities.RandRange(0, Turns.AudioDistractionsRate) == 0)
			{
				_VoiceDirections[Utilities.RandRange(0, _VoiceDirections.length - 1)].play();
			}
		}
		
		private function InitMovingArrows(pNumber:Number):void
		{
			for (var i:Number = 0; i < pNumber; ++i)
			{
				var arrow:Arrow = new Arrow(_Parent);
				arrow.alpha = _Alpha;
				var turnDetails:Object = 
				{
					Color: Turns.GetRandomArrowColor(),
					Orientation: Turns.GetRandomDirection(),
					Motion: Turns.GetRandomDirection(),
					MilliSecondsPerBeat: Turns.GetMilliSecondsPerBeat(_Parent.Speed)
				};
				arrow.Reset(turnDetails, true, false); 
				Utilities.AddChildToDisplayList(this, arrow);
			}
		}
		
		private function InitSpinningArrows(pNumber:Number):void
		{
			_SpinningArrows = new Array();
			for (var i:Number = 0; i < pNumber; ++i)
			{
				var arrow:Arrow = new Arrow(_Parent);
				arrow.alpha = _Alpha;
				var turnDetails:Object = 
				{
					Color: Turns.GetRandomArrowColor(),
					Orientation: Turns.GetRandomDirection(),
					Motion: Turns.GetRandomDirection(),
					MilliSecondsPerBeat: Turns.GetMilliSecondsPerBeat(_Parent.Speed)
				};
				arrow.Reset(turnDetails, true, true); 
				Utilities.AddChildToDisplayList(this, arrow);
			}
		}
	}
}