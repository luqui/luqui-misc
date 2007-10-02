package com.learningrx.MotorTapBeat {
	
import com.learningrx.*;
import com.learningrx.Screens.*;

public class MotorTapBeat extends Game {
	
	private var m_avcue:RhythmGameAVCue;
	private var m_arrowKeyHandler:ArrowKeyHandler;
	
	function MotorTapBeat(pParent:Framework) {
		super(pParent, 'MotorTapBeat', com.learningrx.MotorTapBeat.Turns);
		m_arrowKeyHandler = new ArrowKeyHandler(this);
		m_arrowKeyHandler.Enable();
	}
	
	public override function StartRound(pLevel:Number, pSubLevel:Number, pSpeed:Number):void {
		super.StartRound(pLevel, pSubLevel, pSpeed);
		_Parent.ShowScoreAndDivider(true);
	}
	
	public override function OnStartRoundButtonClicked():void {
		super.OnStartRoundButtonClicked();
		m_avcue = new RhythmGameAVCue(this, bpmToDelay(120.0), 2);
		m_avcue.x = BackgroundWidth/2;
		m_avcue.y = BackgroundHeight/2;
		addChild(m_avcue);
		m_avcue.begin()
	}
	
	public override function ResetEverything():void {
		super.ResetEverything();
		if (m_avcue != null) {
			removeChild(m_avcue);
			m_avcue.end();
			m_avcue = null;
		}
	}
	
	public function OnArrowKeyPressed(dir:String):void {
		m_avcue.OnArrowKeyPressed(dir);
	}
	
	private static function bpmToDelay(bpm:Number):Number {
		return 60000 / bpm;
	}
	
	public function ScoreRight():void {
		++_RightAnswers;
		_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
	}
	
	public function ScoreWrong(): void {
		++_WrongAnswers;
		_Parent.UpdateScoreDisplay(_RightAnswers, _WrongAnswers);
	}
}
	
}
