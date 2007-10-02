package com.learningrx.MotorTapBeat {
	
import com.learningrx.*;
import com.learningrx.Screens.*;

public class MotorTapBeat extends Game {
	
	private var m_level:RhythmGame;
	private var m_arrowKeyHandler:ArrowKeyHandler;
	
	private var m_onStart:Function;
	
	function MotorTapBeat(pParent:Framework) {
		super(pParent, 'MotorTapBeat', com.learningrx.MotorTapBeat.Turns);
		m_arrowKeyHandler = new ArrowKeyHandler(this);
		m_arrowKeyHandler.Enable();
	}
	
	public override function StartRound(pLevel:Number, pSubLevel:Number, pSpeed:Number):void {
		super.StartRound(pLevel, pSubLevel, pSpeed);
		_Parent.ShowScoreAndDivider(true);
		
		var rules = [
			[ // level 1
				{ bpm: 120.0, modulus: 2, audioCue: true, visualCue: true },
				{ bpm: 60.0,  modulus: 2, audioCue: true, visualCue: true },
				{ bpm: 30.0,  modulus: 2, audioCue: true, visualCue: true },
			],
			[ // level 2
			    { bpm: 60.0,  modulus: 1, audioCue: true, visualCue: false },
				{ bpm: 30.0,  modulus: 1, audioCue: true, visualCue: false },
				{ bpm: 15.0,  modulus: 1, audioCue: true, visualCue: false },
			],
			[ // level 3
			 	{ bpm: 60.0,  modulus: 1, audioCue: false, visualCue: true },
				{ bpm: 30.0,  modulus: 1, audioCue: false, visualCue: true },
				{ bpm: 15.0,  modulus: 1, audioCue: false, visualCue: true },
			],
		];
		
		if (pLevel <= 3) {
			var rule = rules[pLevel-1][pSubLevel-1];
			
			m_onStart = function ():void {
				var avcue:RhythmGameAVCue = new RhythmGameAVCue(this, bpmToDelay(rule.bpm), rule.modulus);
				avcue.x = BackgroundWidth/2;
				avcue.y = BackgroundHeight/2;
				avcue.setAudioCue(rule.audioCue);
				avcue.setVisualCue(rule.visualCue);
				addChild(avcue);
				avcue.begin();
				m_level = avcue;
			};
		}
		else {
			m_onStart = function ():void {
				var game = new RhythmGameToneHearing(this, bpmToDelay(60));;
				game.x = BackgroundWidth/2;
				game.y = BackgroundHeight/2;
				addChild(game);
				game.begin();
				m_level = game;
			};
		}
	}
	
	public override function OnStartRoundButtonClicked():void {
		super.OnStartRoundButtonClicked();
		m_onStart();  // set by StartRound above
	}
	
	public override function ResetEverything():void {
		super.ResetEverything();
		if (m_level != null) {
			removeChild(m_level);
			m_level.end();
			m_level = null;
		}
	}
	
	public override function EndRound():void {
		super.EndRound();
		removeChild(m_level);
		m_level.end();
		m_level = null;
	}
	
	public function OnArrowKeyPressed(dir:String):void {
		m_level.OnArrowKeyPressed(dir);
	}
	
	private static function bpmToDelay(bpm:Number):Number {
		return 60000 / bpm;
	}
	
	public function ScoreRight():void {
		++_RightAnswers;
		if (_RightAnswers + _WrongAnswers > 10) { EndRound(); }
		_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
	}
	
	public function ScoreWrong(): void {
		++_WrongAnswers;
		if (_RightAnswers + _WrongAnswers > 10) { EndRound(); }
		_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
	}
}
	
}
