package com.learningrx
{
	import flash.display.Sprite;
	import flash.display.Stage;
	import flash.text.*;
	import flash.events.Event;
	import flash.events.EventPhase;
	import flash.events.MouseEvent;
   import flash.events.KeyboardEvent;

	import com.learningrx.Screens.*;
	import com.learningrx.AttentionArrows.AttentionArrows;
	import com.learningrx.ComprehensionFigures.ComprehensionFigures;
	import com.learningrx.FixationNumbers.FixationNumbers;
	import com.learningrx.MotorTapBeat.MotorTapBeat;

	public class Framework extends Sprite
	{
		public static const ROUND_TIMER_INTERVAL:Number = 100; // lower means smoother animation
		public const FRAMEWORK_WIDTH:Number = 960;
		public const FRAMEWORK_HEIGHT:Number = 750;
		public const GAME_WIDTH:Number = 890;
		public const GAME_HEIGHT:Number = 680;
		public const GAME_X:Number = (FRAMEWORK_WIDTH - GAME_WIDTH) / 2;
		public const GAME_Y:Number = (FRAMEWORK_HEIGHT - GAME_HEIGHT) / 2;

		private var _Copyright:TextField;
		private var _KeyDownListeners:Array;
		private var _ClickSound:Sound_Click = new Sound_Click();
		private var _MenuButton:MenuButton;
		private var _MainMenu:MainMenu;
		private var _Instructions:Instructions;
		private var _StartRoundButton:StartRoundButton;
		private var _OKButton1:OKButton;
		private var _OKButton2:OKButton;
		private var _Game:Game;
		private var _Border:Border;
		private var _ResultsText:ResultsText;
		private var _ScoreAndDivider:ScoreAndDivider;
		private var _AttentionArrows:Game;
		private var _ComprehensionFigures:Game;
		private var _FixationNumbers:Game;
		private var _MotorTapBeat:Game;
      private var _KeysDown:Object = new Object();
		
		public function Framework()
		{
			ShowCopyright();
			InitKeyListeners();
			InitScreens();
			ShowMainMenu();
		}
		
		public function ShowGame(pLevel:Object):void
		{
			Hide(_MainMenu);
			_Game = pLevel.Game;
			_Game.x = GAME_X;
			_Game.y = GAME_Y;
			_Game.StartRound(pLevel.Level, pLevel.Sublevel, pLevel.Speed);
			_Instructions.SetText(pLevel.Instructions);
			_ResultsText.SetText(pLevel.Instructions);
			Show(_Game, _MenuButton, _StartRoundButton, _Instructions, _OKButton1);
			Utilities.MoveChildToTopOfDisplayList(this, _Border);
		}
		
		public function OnStartRoundButtonClicked(pEvent:MouseEvent):void
		{
			PlayClick();
			Hide(_StartRoundButton);
			//stage.focus = _Game;
			_Game.OnStartRoundButtonClicked();
		}
		
		public function EndRound(pRightAnswers:Number, pWrongAnswers:Number):void
		{
			_ResultsText.PercentageCorrect = pRightAnswers / (pRightAnswers + pWrongAnswers) * 100;
			Show(_ResultsText, _OKButton2);
		}
		
		public function OnInstructionsOKButtonClick(pEvent:MouseEvent):void
		{
			Hide(_Instructions, _OKButton1);
		}
		
		public function OnResultsTextOKButtonClick(pEvent:MouseEvent):void
		{
			Hide(_ResultsText, _OKButton2);
			ShowMainMenu();
		}
		
		public function UpdateScoreDisplay(pRightAnswers:Number, 
		                                   pWrongAnswers:Number):void
		{
			_ScoreAndDivider.UpdateScoreDisplay(pRightAnswers, pWrongAnswers);
		}
		
		public function UpdateProgressBar(pPercentage:Number):void
		{
			_ScoreAndDivider.UpdateProgressBar(pPercentage);
		}
			
		public function ShowScoreAndDivider(pShowScore:Boolean = true):void
		{
			Show(_ScoreAndDivider);
		}

		public function HideGame()
		{
			if (null != _Game)
			{
				_Game.ResetEverything();
			}
			UpdateProgressBar(0);
			Hide(_Game, _MenuButton);
		}
		
		public function ShowMainMenu(...args)
		{
			HideGame();
			Show(_MainMenu);
			Hide(_ScoreAndDivider, _MenuButton, _StartRoundButton, _Instructions, _OKButton1, _OKButton2);
		}
		
		public function PlayClick():void
		{
			_ClickSound.play(0, 1);
		}

		public function ToggleFullScreen():void 
		{
			switch(stage.displayState) 
			{
				case "normal":
					stage.displayState = "fullScreen";    
					break;
				case "fullScreen":
				default:
					stage.displayState = "normal";    
					break;
			}
		}
		
		private function InitKeyListeners():void 
		{
			stage.addEventListener(KeyboardEvent.KEY_DOWN, OnKeyDown);
			stage.addEventListener(KeyboardEvent.KEY_DOWN, OnKeyDown, true);
         stage.addEventListener(KeyboardEvent.KEY_UP, OnKeyUp);
         stage.addEventListener(Event.DEACTIVATE, ClearKeys);
			_KeyDownListeners = new Array();
      }
       
      public function AddKeyDownListener(pFunction:Function):void 
		{
         if (!Utilities.ArrayContains(_KeyDownListeners, pFunction))
			{
				_KeyDownListeners.push(pFunction);
			}
      }
       
      public function RemoveKeyDownListener(pFunction:Function):void 
		{
         if (Utilities.ArrayContains(_KeyDownListeners, pFunction))
			{
				Utilities.RemoveElementFromArray(_KeyDownListeners, pFunction);
			}
      }
       
      public function IsDown(pKeyCode:Number):Boolean 
		{
         return Boolean(pKeyCode in _KeysDown);
      }

      private function OnKeyDown(pEvent:KeyboardEvent):void 
		{
			if (pEvent.eventPhase == EventPhase.BUBBLING_PHASE)
			{
				return;
			}
			_KeysDown[pEvent.keyCode] = true;
			for (var i:Number = 0; i < _KeyDownListeners.length; ++i)
			{
				_KeyDownListeners[i](pEvent);
			}
      }
       
      private function OnKeyUp(pEvent:KeyboardEvent):void 
		{
         if (pEvent.keyCode in _KeysDown) 
			{
            delete _KeysDown[pEvent.keyCode];
         }
      }
       
      // clear all keys in _KeysDown since the player cannot
      // detect keys being pressed or released when not focused
      private function ClearKeys(pEvent:Event):void 
		{
         _KeysDown = new Object();
      }
		
		private function InitScreens():void
		{
			_ScoreAndDivider = new ScoreAndDivider(this);
			_ScoreAndDivider.x = GAME_X;
			_ScoreAndDivider.y = GAME_Y + GAME_HEIGHT - _ScoreAndDivider.height - 15;
			_AttentionArrows = new com.learningrx.AttentionArrows.AttentionArrows(this);
			_ComprehensionFigures = new com.learningrx.ComprehensionFigures.ComprehensionFigures(this);
			_FixationNumbers = new com.learningrx.FixationNumbers.FixationNumbers(this);
			_MotorTapBeat = new com.learningrx.MotorTapBeat.MotorTapBeat(this);
			_ResultsText = new ResultsText(this);
			_ResultsText.x = (FRAMEWORK_WIDTH - _ResultsText.width) / 2;
			_ResultsText.y = (FRAMEWORK_HEIGHT - _ResultsText.height) / 2 - 4;
			_StartRoundButton = new StartRoundButton();
			_StartRoundButton.x = (FRAMEWORK_WIDTH - _StartRoundButton.width) / 2;
			_StartRoundButton.y = _ScoreAndDivider.y- 100;
			_StartRoundButton.addEventListener(MouseEvent.CLICK, OnStartRoundButtonClicked);
			_Border = new Border();
			_Border.x = (FRAMEWORK_WIDTH - _Border.width) / 2;
			_Border.y = (FRAMEWORK_HEIGHT - _Border.height) / 2;
			_MainMenu = new MainMenu(this);
			_MainMenu.x = (FRAMEWORK_WIDTH - _MainMenu.width) / 2;
			_MainMenu.y = (FRAMEWORK_HEIGHT - _MainMenu.height) / 2;
			_MenuButton = new MenuButton;
			_MenuButton.x = 70;
			_MenuButton.y = FRAMEWORK_HEIGHT - 78;
			_MenuButton.addEventListener(MouseEvent.CLICK, ShowMainMenu);
			_ResultsText = new ResultsText(this);
			_ResultsText.x = (FRAMEWORK_WIDTH - _ResultsText.width) / 2;
			_ResultsText.y = (GAME_Y + _ScoreAndDivider.y - _ResultsText.height) / 2;
			_Instructions = new Instructions();
			_Instructions.x = (FRAMEWORK_WIDTH - _Instructions.width) / 2;
			_Instructions.y = (GAME_Y + _ScoreAndDivider.y - _Instructions.height) / 2;
			_OKButton1 = new OKButton;
			_OKButton2 = new OKButton;
			_OKButton1.x = _OKButton2.x = (FRAMEWORK_WIDTH - _OKButton1.width) / 2;
			_OKButton1.y = _OKButton2.y = _Instructions.y + _Instructions.height - 120;			
			_OKButton1.addEventListener(MouseEvent.CLICK, OnInstructionsOKButtonClick);
			_OKButton2.addEventListener(MouseEvent.CLICK, OnResultsTextOKButtonClick);
			Show(_Border);
		}
		
		private function ShowCopyright()
		{
			_Copyright = new TextField();
			_Copyright.antiAliasType = flash.text.AntiAliasType.ADVANCED;
			_Copyright.embedFonts = true;
			_Copyright.autoSize = TextFieldAutoSize.LEFT
			_Copyright.selectable = false;
			var format:TextFormat = new TextFormat();
			format.font = 'Arial Rounded MT Bold';
			format.color = 0x3399ff;
			format.size = 8;
			_Copyright.defaultTextFormat = format;
			_Copyright.text = 'Copyright (c) 2007 LearningRx, Inc.';
			_Copyright.x = (FRAMEWORK_WIDTH - _Copyright.textWidth) / 2;
			_Copyright.y = FRAMEWORK_HEIGHT - _Copyright.textHeight - 24;
			Show(_Copyright);
		}
		
		private function Show(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.AddChildToDisplayList(this, args[i]);
			}
		}

		private function Hide(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.RemoveChildFromDisplayList(this, args[i]);
			}
		}
		
		public function get ScoreAndDividerY():Number
		{
			return _ScoreAndDivider.y - GAME_Y;
		}

		public function get AttentionArrows():Game
		{
			return _AttentionArrows;
		}
		
		public function get ComprehensionFigures():Game
		{
			return _ComprehensionFigures;
		}
		
		public function get FixationNumbers():Game
		{
			return _FixationNumbers;
		}

		public function get MotorTapBeat():Game
		{
			return _MotorTapBeat;
		}
	}
}
